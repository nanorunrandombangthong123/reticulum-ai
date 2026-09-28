import crypto from 'crypto';

/**
 * RETICULUM AI PROTOCOL - RANDOMX CPU POW ENGINE (optimized build)
 *
 * CONSENSUS-IDENTICAL to the previous randomx.ts: every hash for every block
 * height / seed is byte-for-byte the same. Only the slow parts were rewritten:
 *   - keystream -> scratchpad copy: a zero-copy BigInt64Array view over the AES
 *     output instead of 262,144 readBigInt64LE() calls (each allocates a BigInt)
 *   - v2.2 full-scratchpad fold: XOR in 32-bit lanes instead of 262,144 BigInt XORs
 *   - no per-hash 2 MB zero buffer allocation
 * The VM loop, seed rules, fork heights and digest layout are untouched.
 *
 * v1:   32 KB scratchpad, 64 VM iterations   (blocks <  FORK_BLOCK_HEIGHT)
 * v2.1: 2 MB scratchpad, AES-CTR keystream   (FORK_BLOCK_HEIGHT .. FORK_V2_2_BLOCK_HEIGHT-1)
 * v2.2: 2 MB chained AES-256-CBC + full 2 MB fold (blocks >= FORK_V2_2_BLOCK_HEIGHT)
 */

const IS_LITTLE_ENDIAN = new Uint8Array(new Uint16Array([1]).buffer)[0] === 1;

export class CortexRandomX {
    public static readonly FORK_BLOCK_HEIGHT = 36040;      // v2.1 Activation Block
    public static readonly FORK_V2_2_BLOCK_HEIGHT = 37825; // v2.2 Anti-GPU Titan-CPU Hard Fork Block

    public static readonly SCRATCHPAD_WORDS_V1 = 4096;   // 32 KB (4096 * 8 bytes)
    public static readonly SCRATCHPAD_WORDS_V2 = 262144; // 2 MB (262144 * 8 bytes = 2,097,152 bytes)
    public static readonly VM_ITERATIONS_V1 = 64;
    public static readonly VM_ITERATIONS_V2 = 128;
    public static readonly EPOCH_BLOCKS = 2048;

    // Pre-allocated static buffers to avoid GC pressure
    private static readonly sharedScratchpadV1 = new BigInt64Array(CortexRandomX.SCRATCHPAD_WORDS_V1);
    private static readonly sharedRegisters = new BigInt64Array(8);
    private static readonly sharedFloats = new Float64Array(4);
    private static readonly sharedFinalBuf = Buffer.alloc(64);
    private static readonly sharedFoldLanes = new Int32Array(128); // 512-byte fold buffer as 32-bit lanes
    private static readonly zeroInputV2 = Buffer.alloc(CortexRandomX.SCRATCHPAD_WORDS_V2 * 8);

    /** View the AES output as the scratchpad without copying (falls back to an exact copy if unsafe). */
    private static scratchpadFromKeystream(keystream: Buffer, words: number): BigInt64Array {
        if (IS_LITTLE_ENDIAN && keystream.byteOffset % 8 === 0) {
            return new BigInt64Array(keystream.buffer, keystream.byteOffset, words);
        }
        const sp = new BigInt64Array(words);
        for (let i = 0; i < words; i++) {
            sp[i] = keystream.readBigInt64LE(i * 8);
        }
        return sp;
    }

    /**
     * Compute RandomX hash of a block header.
     * Selects v1 (32KB), v2.1 (2MB CTR), or v2.2 (2MB Chained CBC + Full 2MB Sponge Fold).
     */
    public static hash(header: string, seed: string = 'cortex-randomx-genesis-seed-v1', blockIndex?: number): string {
        const isV22 = (blockIndex !== undefined && blockIndex >= this.FORK_V2_2_BLOCK_HEIGHT) ||
                      seed.includes('v2.2') ||
                      seed.includes('reticulum-randomx-v2.2');

        const isV2 = isV22 ||
                     (blockIndex !== undefined && blockIndex >= this.FORK_BLOCK_HEIGHT) ||
                     seed.includes('v2') ||
                     seed.includes('reticulum-randomx-v2');

        const words = isV2 ? this.SCRATCHPAD_WORDS_V2 : this.SCRATCHPAD_WORDS_V1;
        const iterations = isV2 ? this.VM_ITERATIONS_V2 : this.VM_ITERATIONS_V1;
        const r = this.sharedRegisters;
        const f = this.sharedFloats;

        // Step 1: Initialize Scratchpad using Seed & Header
        let scratchpad: BigInt64Array;
        if (!isV2) {
            // v1 (32KB): historical SHA-512 expansion (100% exact backward compatibility)
            scratchpad = this.sharedScratchpadV1;
            let key = crypto.createHash('sha512').update(`${header}:${seed}`).digest();
            for (let i = 0; i < words; i += 8) {
                for (let j = 0; j < 8; j++) {
                    scratchpad[i + j] = key.readBigInt64LE((j * 8) % 64);
                }
                if (i % 64 === 0) {
                    key = crypto.createHash('sha512').update(key).digest();
                }
            }
        } else if (isV22) {
            // v2.2 Titan-CPU: AES-256-CBC chained sequential fill
            const seedKey = crypto.createHash('sha256').update(`${header}:${seed}`).digest();
            const iv = crypto.createHash('sha256').update(`${seed}:${header}:v2.2-iv`).digest().subarray(0, 16);
            const cipher = crypto.createCipheriv('aes-256-cbc', seedKey, iv);
            cipher.setAutoPadding(false);
            scratchpad = this.scratchpadFromKeystream(cipher.update(this.zeroInputV2), words);
        } else {
            // v2.1 (2MB AES-CTR): historical blocks 36040 to 37824
            const seedKey = crypto.createHash('sha256').update(`${header}:${seed}`).digest();
            const iv = Buffer.alloc(16, 0);
            const cipher = crypto.createCipheriv('aes-256-ctr', seedKey, iv);
            scratchpad = this.scratchpadFromKeystream(cipher.update(this.zeroInputV2), words);
        }

        // Step 2: Initialize Registers
        const initialDigest = crypto.createHash('sha512').update(`${seed}:${header}`).digest();
        for (let i = 0; i < 8; i++) {
            r[i] = initialDigest.readBigInt64LE(i * 8);
        }
        for (let i = 0; i < 4; i++) {
            f[i] = Number(r[i] % 1000000n) / 1000.0;
        }

        // Step 3: Random Instruction VM Execution Loop (unchanged)
        const mask = words - 1;
        const seedBytes = Buffer.from(seed, 'utf8');

        for (let iter = 0; iter < iterations; iter++) {
            const opCode = (initialDigest[iter % 64] ^ seedBytes[iter % seedBytes.length]) % 10;
            const srcIdx = (iter + 1) % 8;
            const dstIdx = iter % 8;
            const memIdx = Number(BigInt.asUintN(32, r[dstIdx])) & mask;

            switch (opCode) {
                case 0: // IADD_RS
                    r[dstIdx] = (r[dstIdx] + scratchpad[memIdx]) & 0xFFFFFFFFFFFFFFFFn;
                    break;
                case 1: // ISUB_R
                    r[dstIdx] = (r[dstIdx] - r[srcIdx]) & 0xFFFFFFFFFFFFFFFFn;
                    break;
                case 2: // IMUL_R
                    r[dstIdx] = (r[dstIdx] * (r[srcIdx] | 1n)) & 0xFFFFFFFFFFFFFFFFn;
                    break;
                case 3: // IXOR_R
                    r[dstIdx] = r[dstIdx] ^ r[srcIdx];
                    break;
                case 4: // IROL_R
                    const shift = Number(r[srcIdx] & 63n);
                    r[dstIdx] = ((r[dstIdx] << BigInt(shift)) | (r[dstIdx] >> BigInt(64 - shift))) & 0xFFFFFFFFFFFFFFFFn;
                    break;
                case 5: // MEMORY_WRITE
                    scratchpad[memIdx] = r[dstIdx] ^ BigInt(iter);
                    break;
                case 6: // FADD_R
                    f[dstIdx % 4] = f[dstIdx % 4] + f[srcIdx % 4];
                    r[dstIdx] = r[dstIdx] ^ BigInt(Math.floor(Math.abs(f[dstIdx % 4])));
                    break;
                case 7: // FMUL_R
                    f[dstIdx % 4] = f[dstIdx % 4] * 1.00001;
                    r[dstIdx] = r[dstIdx] ^ BigInt(Math.floor(Math.abs(f[dstIdx % 4])));
                    break;
                case 8: // MEMORY_SWAP
                    const nextMem = (memIdx + 64) & mask;
                    const temp = scratchpad[memIdx];
                    scratchpad[memIdx] = scratchpad[nextMem];
                    scratchpad[nextMem] = temp;
                    break;
                case 9: // INEG_R
                    r[dstIdx] = (-r[dstIdx]) & 0xFFFFFFFFFFFFFFFFn;
                    break;
            }
        }

        // Step 4: Final Sponge Digest
        for (let i = 0; i < 8; i++) {
            this.sharedFinalBuf.writeBigInt64LE(r[i], i * 8);
        }

        const h1 = crypto.createHash('sha256').update(this.sharedFinalBuf).digest();

        if (isV22) {
            // v2.2: XOR-fold all 2,097,152 bytes into 512 bytes. XOR is bytewise, so folding in
            // 32-bit lanes over the same memory gives exactly the same 512 bytes as 64-bit lanes.
            const lanes = new Int32Array(scratchpad.buffer, scratchpad.byteOffset, words * 2);
            const fold = this.sharedFoldLanes;
            fold.fill(0);
            for (let i = 0; i < lanes.length; i += 128) {
                for (let j = 0; j < 128; j++) {
                    fold[j] ^= lanes[i + j];
                }
            }
            const foldBytes = Buffer.from(fold.buffer, fold.byteOffset, 512);
            return crypto.createHash('sha256').update(Buffer.concat([h1, foldBytes])).digest('hex');
        } else {
            // Historical v1 / v2.1 digest (first 512 bytes)
            return crypto.createHash('sha256').update(Buffer.concat([h1, Buffer.from(scratchpad.buffer, scratchpad.byteOffset, 512)])).digest('hex');
        }
    }

    public static verify(header: string, hash: string, difficulty: number, seed?: string, blockIndex?: number): boolean {
        const targetPrefix = '0'.repeat(difficulty);
        if (!hash.startsWith(targetPrefix)) return false;
        const calculated = this.hash(header, seed, blockIndex);
        return calculated === hash;
    }

    public static getSeedForBlock(blockIndex: number): string {
        const epoch = Math.floor(blockIndex / this.EPOCH_BLOCKS);
        if (blockIndex >= this.FORK_V2_2_BLOCK_HEIGHT) {
            return `reticulum-randomx-v2.2-epoch-${epoch}`;
        }
        if (blockIndex >= this.FORK_BLOCK_HEIGHT) {
            return `reticulum-randomx-v2-epoch-${epoch}`;
        }
        return `cortex-randomx-epoch-${epoch}`;
    }

    /**
     * Short fingerprints of fixed test vectors. Run on two machines (or PC vs server):
     * if any line differs, their randomx.ts versions produce different hashes.
     *   node -e "console.log(require('./dist/core/randomx').CortexRandomX.fingerprint())"
     */
    public static fingerprint(): Record<string, string> {
        const vec = (blockIndex: number) =>
            this.hash('fingerprint-vector', this.getSeedForBlock(blockIndex), blockIndex).slice(0, 16);
        return {
            v1_block_100: vec(100),
            v2_1_block_36040: vec(this.FORK_BLOCK_HEIGHT),
            v2_2_block_37825: vec(this.FORK_V2_2_BLOCK_HEIGHT),
            v2_2_block_62125: vec(62125)
        };
    }
}
