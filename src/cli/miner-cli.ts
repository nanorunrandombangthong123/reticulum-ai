import os from 'os';
import fs from 'fs';
import path from 'path';
import readline from 'readline';
import { Worker, isMainThread, parentPort, workerData } from 'worker_threads';
import { CortexCrypto } from '../core/crypto';
import { CortexRandomX } from '../core/randomx';

// =============================================================================
// WORKER THREAD: hashes in short time slices so it reports progress often,
// keeps its nonce per job, and reports crashes back to the main thread.
// =============================================================================
function runWorker() {
    const threadId = Number(workerData?.threadId) || 0;
    const totalThreads = Number(workerData?.totalThreads) || 1;
    const SLICE_MS = 200;

    let job: any = null;
    let nonce = 0;
    let readyReported = false;

    parentPort?.on('message', (msg: any) => {
        if (msg.type === 'job') {
            job = msg.job;
            nonce = Math.floor(Math.random() * 50_000_000) * totalThreads + threadId;
        } else if (msg.type === 'stop') {
            process.exit(0);
        }
    });

    function loop() {
        if (!job) {
            setTimeout(loop, 50);
            return;
        }
        const j = job;
        const started = Date.now();
        let count = 0;

        try {
            do {
                const header = `${j.headerPrefix}${nonce}${j.headerSuffix}`;
                const hash = CortexRandomX.hash(header, j.seed, j.templateIndex);
                count++;
                if (hash.startsWith(j.targetPrefix)) {
                    parentPort?.postMessage({ type: 'found', nonce, hash, templateIndex: j.templateIndex, jobId: j.jobId });
                }
                nonce += totalThreads;
            } while (Date.now() - started < SLICE_MS);
        } catch (e: any) {
            parentPort?.postMessage({ type: 'error', message: String(e?.message || e) });
            setTimeout(loop, 2000);
            return;
        }

        if (!readyReported) {
            readyReported = true;
            parentPort?.postMessage({ type: 'ready', firstSliceMs: Date.now() - started });
        }
        parentPort?.postMessage({ type: 'hashes', count });
        setImmediate(loop); // lets 'job' / 'stop' messages through between slices
    }

    loop();
}

// =============================================================================
// MAIN THREAD
// =============================================================================
let NODE_URL = process.env.NODE_URL || 'https://reticulum-ai.xyz';
let minerAddress = process.env.MINER_ADDRESS || '';
let allocatedThreads = Number(process.env.MINER_THREADS) || Math.max(1, Math.floor(os.cpus().length / 2));
let miningMode: 'pool' | 'solo' = 'pool';
let workerId = 'worker-1';

const CONFIG_DIR = path.join(os.homedir(), '.reticulum');
const CONFIG_FILE = path.join(CONFIG_DIR, 'miner_config.json');

let rl: readline.Interface | null = null;

// ---- runtime state ----------------------------------------------------------
let initialBalance = -1;
let lastKnownBalance = 0;
let localBlocksFound = 0;
let poolSharesAccepted = 0;
let sharesFoundByWorkers = 0;
let sharesRejected = 0;
let sharesStale = 0;
let localTotalHashes = 0;
let localHashrate = 0;
let workersReady = 0;
let spinnerIdx = 0;
let isMiningRunning = true;
let currentTemplate: any = null;
let currentJobInfo = '';
let latestJobId = 0;
let nextJobId = 1;
let headerDrift = false;
// The exact template each job was built from. Shares MUST be submitted with the
// template their hash was computed from, not with whatever the node returned last.
const jobTemplates = new Map<number, any>();
let lastTemplateAt = 0;
let lastError = '';
let lastErrorAt = 0;
const SPINNERS = ['⠋', '⠙', '⠹', '⠸', '⠼', '⠴', '⠦', '⠧', '⠇', '⠏'];
const activityLog: string[] = [];
const activeWorkers: Worker[] = [];

function sleep(ms: number) {
    return new Promise<void>(r => setTimeout(r, ms));
}

function setError(msg: string) {
    lastError = msg;
    lastErrorAt = Date.now();
}

function logActivity(line: string) {
    activityLog.unshift(line);
    if (activityLog.length > 5) activityLog.pop();
}

function askQuestion(query: string): Promise<string> {
    return new Promise(resolve => rl!.question(query, resolve));
}

function stripAnsi(str: string): string {
    return str.replace(/\x1b\[[0-9;]*m/g, '');
}

function padVisible(str: string, targetLength: number): string {
    return str + ' '.repeat(Math.max(0, targetLength - stripAnsi(str).length));
}

function fmtRate(n: number): string {
    if (n >= 1_000_000) return `${(n / 1_000_000).toFixed(2)} MH/s`;
    if (n >= 1_000) return `${(n / 1_000).toFixed(2)} kH/s`;
    return `${n} H/s`;
}

function loadSavedConfig() {
    try {
        if (fs.existsSync(CONFIG_FILE)) return JSON.parse(fs.readFileSync(CONFIG_FILE, 'utf8'));
    } catch {}
    return null;
}

function saveConfig(config: any) {
    try {
        if (!fs.existsSync(CONFIG_DIR)) fs.mkdirSync(CONFIG_DIR, { recursive: true });
        fs.writeFileSync(CONFIG_FILE, JSON.stringify(config, null, 2), 'utf8');
    } catch (e) {
        console.error('Error saving miner config:', e);
    }
}

function sanitizeNodeUrl(rawUrl: string): string {
    if (!rawUrl) return 'https://reticulum-ai.xyz';
    let clean = rawUrl.trim();
    clean = clean.replace(/::+/g, ':');
    if (clean.includes(':3333')) clean = clean.replace(':3333', '');
    if (!clean.startsWith('http://') && !clean.startsWith('https://')) clean = 'https://' + clean;
    return clean.replace(/\/+$/, '');
}

async function fetchJson(endpoint: string, options: any = {}): Promise<any> {
    const url = `${sanitizeNodeUrl(NODE_URL)}${endpoint}`;
    let res: Response;
    try {
        res = await fetch(url, {
            ...options,
            signal: AbortSignal.timeout(8000),
            body: options.body ? (typeof options.body === 'string' ? options.body : JSON.stringify(options.body)) : undefined,
            headers: {
                'Content-Type': 'application/json',
                'Accept': 'application/json',
                ...(options.headers || {})
            }
        });
    } catch (e: any) {
        throw new Error(`cannot reach ${NODE_URL}: ${e.message}`);
    }
    const text = await res.text();
    try {
        return JSON.parse(text);
    } catch {
        throw new Error(`non-JSON reply (HTTP ${res.status}): ${text.substring(0, 100)}`);
    }
}

// ---- setup / wallet wizard --------------------------------------------------
async function setupMiner() {
    rl = readline.createInterface({ input: process.stdin, output: process.stdout });
    rl.on('SIGINT', shutdown);

    console.log('\x1b[36m╔══════════════════════════════════════════════════════════════════════╗\x1b[0m');
    console.log('\x1b[36m║\x1b[0m   \x1b[1;35m🧠 RETICULUM AI ($RAIX) - HARDWARE CPU & POOL MINER\x1b[0m              \x1b[36m║\x1b[0m');
    console.log('\x1b[36m╚══════════════════════════════════════════════════════════════════════╝\x1b[0m\n');

    const totalCpus = os.cpus().length;
    console.log(`\x1b[32m[SYSTEM]\x1b[0m Detected CPU Hardware: \x1b[1m${os.cpus()[0]?.model || 'Multi-Core CPU'}\x1b[0m`);
    console.log(`\x1b[32m[SYSTEM]\x1b[0m Available Hardware Threads: \x1b[1;33m${totalCpus} Cores/Threads\x1b[0m\n`);

    // CLI: --address/-a, --threads/-t, --mode/-m, --node/-n, --worker/-w
    const args = process.argv.slice(2);
    let cliAddress = process.env.MINER_ADDRESS || '';
    let cliThreads = Number(process.env.MINER_THREADS) || 0;
    let cliMode = (process.env.MINING_MODE as 'pool' | 'solo') || '';
    let cliNode = process.env.NODE_URL || '';
    let cliWorker = '';

    for (let i = 0; i < args.length; i++) {
        if ((args[i] === '--address' || args[i] === '-a') && args[i + 1]) cliAddress = args[++i];
        else if ((args[i] === '--threads' || args[i] === '-t') && args[i + 1]) cliThreads = parseInt(args[++i], 10);
        else if ((args[i] === '--mode' || args[i] === '-m') && args[i + 1]) {
            const m = args[++i].toLowerCase();
            if (m === 'solo' || m === 'pool') cliMode = m;
        } else if ((args[i] === '--node' || args[i] === '-n') && args[i + 1]) cliNode = args[++i];
        else if ((args[i] === '--worker' || args[i] === '-w') && args[i + 1]) cliWorker = args[++i];
    }

    const defaultWorker = os.hostname().substring(0, 12) || 'worker-1';

    if (cliAddress) {
        minerAddress = cliAddress;
        workerId = cliWorker || defaultWorker;
        if (cliThreads && cliThreads >= 1) allocatedThreads = Math.min(cliThreads, totalCpus);
        if (cliMode) miningMode = cliMode;
        if (cliNode) NODE_URL = sanitizeNodeUrl(cliNode);
        console.log(`\x1b[32m[AUTO-START]\x1b[0m Payout Address : \x1b[1;32m${minerAddress}\x1b[0m`);
        console.log(`\x1b[32m[AUTO-START]\x1b[0m Mining Mode    : \x1b[1;35m${miningMode.toUpperCase()}\x1b[0m`);
        console.log(`\x1b[32m[AUTO-START]\x1b[0m CPU Threads    : \x1b[1;33m${allocatedThreads} Threads\x1b[0m`);
        console.log(`\x1b[32m[AUTO-START]\x1b[0m Node URL       : \x1b[1m${NODE_URL}\x1b[0m\n`);

        saveConfig({ minerAddress, miningMode, workerId, threads: allocatedThreads, nodeUrl: NODE_URL, savedAt: new Date().toISOString() });
        console.log('\x1b[35mStarting mining dashboard in 2 seconds...\x1b[0m');
        await sleep(2000);
        return;
    }

    const saved = loadSavedConfig();
    if (saved && saved.minerAddress && !process.env.MINER_ADDRESS) {
        console.log(`\x1b[34m[SAVED CONFIG]\x1b[0m Found existing payout wallet: \x1b[1;32m${saved.minerAddress}\x1b[0m`);
        console.log(`\x1b[34m[SAVED CONFIG]\x1b[0m Mining Mode: \x1b[1;35m${(saved.miningMode || 'pool').toUpperCase()}\x1b[0m`);
        console.log(`\x1b[34m[SAVED CONFIG]\x1b[0m Configured Threads: \x1b[1;33m${saved.threads || allocatedThreads} Threads\x1b[0m`);
        console.log(`\x1b[34m[SAVED CONFIG]\x1b[0m Node URL: \x1b[1m${saved.nodeUrl || NODE_URL}\x1b[0m\n`);

        const answer = await askQuestion('\x1b[1mUse saved configuration? [Y/n]: \x1b[0m');
        if (!answer.trim() || answer.trim().toLowerCase() === 'y') {
            minerAddress = saved.minerAddress;
            miningMode = saved.miningMode || 'pool';
            workerId = saved.workerId || defaultWorker;
            allocatedThreads = Math.min(saved.threads || allocatedThreads, totalCpus);
            NODE_URL = sanitizeNodeUrl(saved.nodeUrl || NODE_URL);
            return;
        }
    }

    console.log('\x1b[1mSelect Mining Strategy:\x1b[0m');
    console.log('  \x1b[36m[1]\x1b[0m \x1b[1;32mCollaborative Mining Pool (Recommended)\x1b[0m - Lower share difficulty, regular PPLNS payouts');
    console.log('  \x1b[36m[2]\x1b[0m \x1b[1;33mSolo Hardware Mining\x1b[0m - Full 50 RAIX block rewards upon solving network difficulty');
    const modeChoice = (await askQuestion('\nSelect mining mode [1-2] (default: 1): ')).trim() || '1';
    miningMode = modeChoice === '2' ? 'solo' : 'pool';

    console.log('\n\x1b[1mPlease choose your Payout Wallet setup:\x1b[0m');
    console.log('  \x1b[36m[1]\x1b[0m Create a NEW $RAIX Wallet (Generates secp256k1 keypair)');
    console.log('  \x1b[36m[2]\x1b[0m Enter my EXISTING $RAIX Address (e.g., ctx1...)');
    console.log('  \x1b[36m[3]\x1b[0m Import via PRIVATE KEY');
    const choice = (await askQuestion('\nSelect wallet option [1-3] (default: 1): ')).trim() || '1';

    if (choice === '1') {
        const keyPair = CortexCrypto.generateKeyPair();
        minerAddress = keyPair.address;
        console.log('\n\x1b[32m✓ NEW WALLET GENERATED SUCCESSFULLY!\x1b[0m');
        console.log(`\x1b[33mPayout Address :\x1b[0m \x1b[1;32m${keyPair.address}\x1b[0m`);
        console.log(`\x1b[31mPrivate Key    :\x1b[0m \x1b[1;31m${keyPair.privateKey}\x1b[0m`);
        console.log('\x1b[90m⚠️  Please save your private key in a secure place!\x1b[0m\n');
    } else if (choice === '2') {
        const addr = (await askQuestion('\x1b[1mEnter your $RAIX payout address (ctx1...): \x1b[0m')).trim();
        if (!addr.startsWith('ctx1') || addr.length < 20) {
            console.log('\x1b[31mInvalid address format. Defaulting to new wallet.\x1b[0m');
            const keyPair = CortexCrypto.generateKeyPair();
            minerAddress = keyPair.address;
            console.log(`\x1b[33mNew Payout Address :\x1b[0m \x1b[1;32m${keyPair.address}\x1b[0m`);
            console.log(`\x1b[31mPrivate Key        :\x1b[0m \x1b[1;31m${keyPair.privateKey}\x1b[0m\n`);
        } else {
            minerAddress = addr;
        }
    } else if (choice === '3') {
        const priv = (await askQuestion('\x1b[1mEnter your private key (64 hex characters): \x1b[0m')).trim();
        try {
            const keyPair = CortexCrypto.fromPrivateKey(priv);
            minerAddress = keyPair.address;
            console.log(`\x1b[32m✓ Wallet imported successfully! Address: ${minerAddress}\x1b[0m\n`);
        } catch {
            console.log('\x1b[31mInvalid private key. Generating new wallet.\x1b[0m');
            const keyPair = CortexCrypto.generateKeyPair();
            minerAddress = keyPair.address;
            console.log(`\x1b[33mNew Payout Address :\x1b[0m \x1b[1;32m${keyPair.address}\x1b[0m`);
            console.log(`\x1b[31mPrivate Key        :\x1b[0m \x1b[1;31m${keyPair.privateKey}\x1b[0m\n`);
        }
    }

    const workerInput = (await askQuestion(`\nEnter Worker Identifier (default: ${defaultWorker}): `)).trim();
    workerId = workerInput || defaultWorker;

    console.log(`\n\x1b[1mConfigure CPU Mining Power:\x1b[0m`);
    const threadsInput = await askQuestion(`Enter number of threads to allocate [1-${totalCpus}] (default: ${Math.max(1, Math.floor(totalCpus / 2))}): `);
    const parsedThreads = Number(threadsInput.trim());
    if (parsedThreads >= 1 && parsedThreads <= totalCpus) allocatedThreads = parsedThreads;

    const nodeInput = await askQuestion(`\nEnter Reticulum Node URL (default: ${NODE_URL}): `);
    if (nodeInput.trim()) NODE_URL = sanitizeNodeUrl(nodeInput.trim());

    saveConfig({ minerAddress, miningMode, workerId, threads: allocatedThreads, nodeUrl: NODE_URL, savedAt: new Date().toISOString() });
    console.log('\n\x1b[32m✓ Configuration saved to ~/.reticulum/miner_config.json\x1b[0m');
    console.log('\x1b[35mStarting mining dashboard in 2 seconds...\x1b[0m');
    await sleep(2000);
}

// ---- share / block submission ----------------------------------------------
async function handleFoundShare(nonce: number, hash: string, templateIndex: number, jobId: number) {
    sharesFoundByWorkers++;
    const tpl = jobTemplates.get(jobId);
    if (!tpl || jobId !== latestJobId) {
        sharesStale++;
        return;
    }

    const payload = {
        minerAddress,
        workerId,
        hashrate: localHashrate,
        index: tpl.index,
        previousHash: tpl.previousHash,
        timestamp: tpl.timestamp,
        transactions: tpl.transactions,
        difficulty: tpl.difficulty,
        nonce,
        hash
    };

    const timeStr = new Date().toLocaleTimeString();
    try {
        const endpoint = miningMode === 'pool' ? '/api/pool/submit-share' : '/api/miner/submit-block';
        const res = await fetchJson(endpoint, { method: 'POST', body: payload });

        if (miningMode === 'pool') {
            if (res.validShare) {
                poolSharesAccepted++;
                if (res.blockFound) {
                    localBlocksFound++;
                    logActivity(`\x1b[1;35m🎉🎉 [${timeStr}] JACKPOT! Block #${templateIndex} found for the pool!\x1b[0m`);
                } else {
                    logActivity(`\x1b[1;32m✓ [${timeStr}] Share accepted (diff ${tpl.shareDifficulty}). Total: ${poolSharesAccepted}\x1b[0m`);
                }
            } else {
                sharesRejected++;
                const why = JSON.stringify(res).slice(0, 120);
                setError(`share REJECTED by node: ${why}`);
                logActivity(`\x1b[31m✗ [${timeStr}] Share rejected: ${why}\x1b[0m`);
            }
        } else {
            if (res.success) {
                localBlocksFound++;
                logActivity(`\x1b[1;32m💎 [${timeStr}] BLOCK #${templateIndex} SOLVED SOLO! +${res.reward || 50} RAIX credited\x1b[0m`);
            } else {
                sharesRejected++;
                const why = JSON.stringify(res).slice(0, 120);
                setError(`block REJECTED by node: ${why}`);
                logActivity(`\x1b[31m✗ [${timeStr}] Block rejected: ${why}\x1b[0m`);
            }
        }
    } catch (e: any) {
        setError(`submit failed: ${e.message}`);
    }
}

// ---- mining engine ----------------------------------------------------------
function startWorkers() {
    let lastTime = Date.now();
    let lastHashes = 0;
    setInterval(() => {
        const now = Date.now();
        const elapsed = (now - lastTime) / 1000;
        if (elapsed >= 0.8) {
            localHashrate = Math.round((localTotalHashes - lastHashes) / elapsed);
            lastTime = now;
            lastHashes = localTotalHashes;
        }
    }, 800);

    for (let t = 0; t < allocatedThreads; t++) {
        const w = new Worker(__filename, { workerData: { threadId: t, totalThreads: allocatedThreads } });
        w.on('message', (msg: any) => {
            if (msg.type === 'hashes') localTotalHashes += msg.count;
            else if (msg.type === 'found') handleFoundShare(msg.nonce, msg.hash, msg.templateIndex, msg.jobId);
            else if (msg.type === 'ready') workersReady++;
            else if (msg.type === 'error') setError(`worker ${t} hash error: ${msg.message}`);
        });
        w.on('error', (err: any) => setError(`worker ${t} crashed: ${err?.message || err}`));
        w.on('exit', (code: number) => {
            if (isMiningRunning) setError(`worker ${t} exited unexpectedly (code ${code})`);
        });
        activeWorkers.push(w);
    }
}

async function templateLoop() {
    while (isMiningRunning) {
        try {
            const endpoint = miningMode === 'pool'
                ? `/api/pool/template?address=${encodeURIComponent(minerAddress)}&worker=${encodeURIComponent(workerId)}&hashrate=${localHashrate}`
                : `/api/miner/template?address=${encodeURIComponent(minerAddress)}`;

            const t = await fetchJson(endpoint);

            if (!t || typeof t.headerPrefix !== 'string' || typeof t.headerSuffix !== 'string') {
                setError(`template has no headerPrefix/headerSuffix: ${JSON.stringify(t).slice(0, 140)}`);
                await sleep(2000);
                continue;
            }

            const targetPrefix = miningMode === 'pool' ? t.targetSharePrefix : t.targetPrefix;
            if (typeof targetPrefix !== 'string' || targetPrefix.length === 0) {
                setError(`template has no ${miningMode === 'pool' ? 'targetSharePrefix' : 'targetPrefix'}: ${JSON.stringify(t).slice(0, 140)}`);
                await sleep(2000);
                continue;
            }

            lastTemplateAt = Date.now();
            const isNew = !currentTemplate || currentTemplate.index !== t.index || currentTemplate.previousHash !== t.previousHash;

            if (isNew) {
                currentTemplate = t;
                const seed = CortexRandomX.getSeedForBlock(t.index);
                const jobId = nextJobId++;
                jobTemplates.set(jobId, t);
                latestJobId = jobId;
                for (const k of [...jobTemplates.keys()]) if (k < jobId - 3) jobTemplates.delete(k);
                headerDrift = false;
                const job = {
                    headerPrefix: t.headerPrefix,
                    headerSuffix: t.headerSuffix,
                    targetPrefix,
                    seed,
                    templateIndex: t.index,
                    jobId
                };
                currentJobInfo = `#${t.index}  target "${targetPrefix}"`;
                for (const w of activeWorkers) w.postMessage({ type: 'job', job });
            } else if (t.headerPrefix !== currentTemplate.headerPrefix || t.headerSuffix !== currentTemplate.headerSuffix) {
                // Node hands out a different header on every poll (e.g. fresh timestamp).
                // Keep hashing and submitting against the job's own template.
                headerDrift = true;
            }
            await sleep(1000);
        } catch (e: any) {
            setError(`template: ${e.message}`);
            await sleep(2000);
        }
    }
}

// ---- dashboard --------------------------------------------------------------
const BOX_W = 70;
const PAD_W = 45;
const hr = () => '═'.repeat(BOX_W);
const boxRow = (color: string, label: string, value: string) =>
    `\x1b[36m║\x1b[0m  ${color}${label.padEnd(20)}\x1b[0m: ${padVisible(value, PAD_W)} \x1b[36m║\x1b[0m`;

async function renderDashboard() {
    const lines: string[] = [];
    try {
        const [stats, poolStats, poolMiner, balanceData] = await Promise.all([
            fetchJson('/api/stats'),
            miningMode === 'pool' ? fetchJson('/api/pool/stats').catch(() => null) : Promise.resolve(null),
            miningMode === 'pool' && minerAddress ? fetchJson(`/api/pool/miner/${encodeURIComponent(minerAddress)}`).catch(() => null) : Promise.resolve(null),
            minerAddress ? fetchJson(`/api/balance/${minerAddress}`).catch(() => ({ balance: 0 })) : Promise.resolve({ balance: 0 })
        ]);

        const currentBal = Number(balanceData?.balance) || 0;
        if (initialBalance === -1) {
            initialBalance = currentBal;
            lastKnownBalance = currentBal;
        } else if (currentBal > lastKnownBalance) {
            logActivity(`\x1b[1;32m💸 [${new Date().toLocaleTimeString()}] PAYOUT CONFIRMED! +${(currentBal - lastKnownBalance).toFixed(4)} $RAIX\x1b[0m`);
            lastKnownBalance = currentBal;
        }
        const onChainGained = Math.max(0, currentBal - initialBalance);

        spinnerIdx = (spinnerIdx + 1) % SPINNERS.length;
        const spinner = SPINNERS[spinnerIdx];

        // Honest engine status (no fake hashrate anymore)
        let engineStr: string;
        if (!currentTemplate) {
            engineStr = `\x1b[1;31m${spinner} WAITING FOR JOB FROM NODE\x1b[0m`;
        } else if (workersReady < allocatedThreads) {
            engineStr = `\x1b[1;33m${spinner} INITIALIZING RandomX (${workersReady}/${allocatedThreads} threads ready)\x1b[0m`;
        } else if (localHashrate === 0) {
            engineStr = `\x1b[1;33m${spinner} WARMING UP...\x1b[0m`;
        } else {
            engineStr = `\x1b[1;32m${spinner} HASHING (${allocatedThreads} threads)\x1b[0m`;
        }

        lines.push(`\x1b[36m╔${hr()}╗\x1b[0m`);
        lines.push(`\x1b[36m║\x1b[0m${padVisible('   \x1b[1;35m🧠 RETICULUM AI ($RAIX) - RANDOMX CPU MINER (TESTNET 2.0)\x1b[0m', BOX_W)}\x1b[36m║\x1b[0m`);
        lines.push(`\x1b[36m╠${hr()}╣\x1b[0m`);

        lines.push(boxRow('\x1b[33m', 'Mining Strategy', miningMode === 'pool' ? '\x1b[1;35m● COLLABORATIVE POOL (PPLNS 1% Fee)\x1b[0m' : '\x1b[1;33m● SOLO HARDWARE MINING (Direct L1)\x1b[0m'));
        lines.push(boxRow('\x1b[33m', 'Worker / Rig ID', `\x1b[1;37m${workerId} (${allocatedThreads} / ${os.cpus().length} Threads)\x1b[0m`));
        lines.push(boxRow('\x1b[33m', 'Payout Address', `\x1b[1;37m${minerAddress.substring(0, 36)}...\x1b[0m`));
        lines.push(boxRow('\x1b[1;32m', 'Wallet Balance', `\x1b[1;32m${currentBal.toFixed(4)} $RAIX\x1b[0m`));

        if (miningMode === 'pool' && poolMiner) {
            const shares = poolMiner.roundShares ?? 'n/a';
            const pct = poolMiner.roundEffortPercent ?? 'n/a';
            lines.push(boxRow('\x1b[33m', 'Round Contribution', `\x1b[1;33m${shares} Shares (${pct}% of Round)\x1b[0m`));
            if (typeof poolMiner.estimatedBlockReward === 'number') {
                lines.push(boxRow('\x1b[33m', 'Est. Block Reward', `\x1b[1;35m~${poolMiner.estimatedBlockReward.toFixed(2)} $RAIX on Block Mined\x1b[0m`));
            }
            if (typeof poolMiner.pendingPayout === 'number') {
                lines.push(boxRow('\x1b[33m', 'Pending Payout', `\x1b[1;33m${poolMiner.pendingPayout.toFixed(4)} $RAIX\x1b[0m`));
            }
        }
        lines.push(boxRow('\x1b[33m', 'Session Earnings', `\x1b[1;33m+${onChainGained.toFixed(4)} $RAIX (on-chain)\x1b[0m`));

        lines.push(`\x1b[36m╠${hr()}╣\x1b[0m`);
        lines.push(boxRow('\x1b[34m', 'Block Height', `\x1b[1;37m#${stats.height}\x1b[0m`));
        lines.push(boxRow('\x1b[34m', 'Network Difficulty', `\x1b[1;37m${stats.difficulty}\x1b[0m`));
        if (miningMode === 'pool' && poolStats) {
            lines.push(boxRow('\x1b[34m', 'Pool Share Diff', `\x1b[1;33m${poolStats.shareDifficulty} (Fast CPU Shares)\x1b[0m`));
            const n = poolStats.connectedMinersCount;
            lines.push(boxRow('\x1b[35m', 'Total Pool Hashrate', `\x1b[1;35m${fmtRate(poolStats.totalPoolHashrate || 0)} (${n} Worker${n === 1 ? '' : 's'})\x1b[0m`));
        }
        lines.push(boxRow('\x1b[34m', 'Global Net Hashrate', `\x1b[1;36m${fmtRate(stats.networkHashrate || 0)} (L1 Consensus)\x1b[0m`));
        lines.push(boxRow('\x1b[34m', 'Total Burned $RAIX', `\x1b[1;31m${(Number(stats.totalBurned) || 0).toFixed(3)} $RAIX 🔥\x1b[0m`));

        lines.push(`\x1b[36m╠${hr()}╣\x1b[0m`);
        lines.push(boxRow('\x1b[32m', 'Hardware Engine', engineStr));
        lines.push(boxRow('\x1b[32m', 'Your Rig Hashrate', `\x1b[1;32m${fmtRate(localHashrate)}\x1b[0m`));
        lines.push(boxRow('\x1b[32m', 'Local Hashes Checked', `${localTotalHashes.toLocaleString()}`));
        const jobAge = lastTemplateAt ? `${Math.round((Date.now() - lastTemplateAt) / 1000)}s ago` : 'never';
        lines.push(boxRow('\x1b[32m', 'Current Job', currentJobInfo ? `${currentJobInfo} (refreshed ${jobAge})` : 'none received yet'));
        if (headerDrift) lines.push(boxRow('\x1b[32m', 'Template Note', '\x1b[90mnode header changes each poll (handled)\x1b[0m'));
        const shareLine = miningMode === 'pool'
            ? `found ${sharesFoundByWorkers} | ok ${poolSharesAccepted} | rej ${sharesRejected} | stale ${sharesStale}`
            : `found ${sharesFoundByWorkers} | blocks ${localBlocksFound} | rej ${sharesRejected} | stale ${sharesStale}`;
        lines.push(boxRow('\x1b[32m', 'Shares', `\x1b[1;33m${shareLine}\x1b[0m`));
        lines.push(`\x1b[36m╚${hr()}╝\x1b[0m`);
    } catch (err: any) {
        lines.push(`\x1b[31m[ERROR] Dashboard update failed: ${err.message}\x1b[0m`);
    }

    if (lastError) {
        const age = Math.round((Date.now() - lastErrorAt) / 1000);
        lines.push(`\n\x1b[1;31m⚠ LAST ERROR (${age}s ago): ${lastError}\x1b[0m`);
    }
    if (activityLog.length > 0) {
        lines.push('\n\x1b[1m📜 Mining Activity & Pool Rewards Log:\x1b[0m');
        activityLog.forEach(l => lines.push('  ' + l));
    }
    lines.push('\n\x1b[90mPress [Ctrl+C] to stop mining.\x1b[0m');

    // single write, no full-screen flash
    process.stdout.write('\x1b[H\x1b[J' + lines.join('\n') + '\n');
}

async function dashboardLoop() {
    while (isMiningRunning) {
        await renderDashboard();
        await sleep(800);
    }
}

// ---- shutdown ---------------------------------------------------------------
function shutdown() {
    isMiningRunning = false;
    for (const w of activeWorkers) {
        try { w.terminate(); } catch {}
    }
    try { rl?.close(); } catch {}
    process.stdout.write('\n\x1b[0mMiner stopped.\n');
    process.exit(0);
}

async function runMain() {
    process.on('SIGINT', shutdown);
    process.on('SIGTERM', shutdown);

    await setupMiner();
    rl?.close(); // otherwise readline swallows Ctrl+C
    rl = null;

    process.stdout.write('\x1b[2J');
    startWorkers();
    templateLoop();
    dashboardLoop();
}

if (isMainThread) {
    runMain();
} else {
    runWorker();
}
