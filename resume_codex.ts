#! /usr/bin/env bun

import { spawn } from "bun";

// ==========================================
// TYPE DEFINITIONS (Functional / Lean Style)
// ==========================================

type TaskConfig = {
    readonly name: string;
    readonly getStartTime: () => Date;
    readonly intervalMs: number;
    readonly getMessage: (iteration: number) => string;
    readonly runner: (msg: string) => Promise<boolean>;
};

type AppConfig = {
    readonly sessionId: string;
    readonly codexMessage: string;
    readonly geminiMessage: string;
    readonly codexIntervalMs: number;
    readonly geminiIntervalMs: number;
    readonly retryDelayMs: number;
    readonly maxRetries: number;
};

type WorkerState = {
    readonly nextRunTime: number;
    readonly iteration: number;
};

type Lock = {
    readonly runExclusive: <T>(action: () => Promise<T>) => Promise<T>;
};

// ==========================================
// IMMUTABLE CONFIGURATION
// ==========================================

const CONFIG: AppConfig = {
    sessionId: "019e926d-d08e-7641-b5b6-3cd26b91f03a",
    codexMessage: "/goal continue fixing. To see goal - read GOAL.md. You are allowed to run long tasks, because I am right now away from keyboard. I have already done some work, so run git diff to verify the current changes; adjust if needed. To see goal - read GOAL.md.",
    geminiMessage: "/goal continue fixing",
    codexIntervalMs: (5 * 60 + 10) * 60 * 1000, // 5h 10m
    geminiIntervalMs: 5 * 60 * 60 * 1000,       // 5h
    retryDelayMs: 5 * 60 * 1000,                // 5m
    maxRetries: 12,
};

// ==========================================
// PURE UTILITY FUNCTIONS
// ==========================================

const sleep = (ms: number): Promise<void> =>
    new Promise((resolve) => setTimeout(resolve, ms));

const getCodexStartTime = (): Date => {
    const target = new Date();
    target.setHours(23, 42, 0, 0);
    target.setSeconds(target.getSeconds() + 60); // 23:43 Buffer
    return target.getTime() < Date.now()
        ? new Date(target.getTime() + 24 * 60 * 60 * 1000)
        : target;
};

const getGeminiStartTime = (): Date => {
    const target = new Date();
    target.setDate(target.getDate() + 1); // Tomorrow
    target.setHours(4, 0, 0, 0);          // 04:00 AM
    return target;
};

/**
 * Creates an asynchronous, functional execution lock (Mutex).
 */
const makeLock = (): Lock => {
    let chain = Promise.resolve();
    return {
        runExclusive: async <T>(action: () => Promise<T>): Promise<T> => {
            const previous = chain;
            let resolveChain: () => void = () => { };

            chain = new Promise<void>((resolve) => {
                resolveChain = resolve;
            });

            await previous;
            try {
                return await action();
            } finally {
                resolveChain();
            }
        }
    };
};

// ==========================================
// IO EFFECT HANDLERS (Shell Execution)
// ==========================================

const runCodexCommand = (sessionId: string) => async (message: string): Promise<boolean> => {
    const process = spawn(["codex", "resume", sessionId, "-m", message], {
        stdout: "pipe",
        stderr: "pipe",
    });

    const stdout = await new Response(process.stdout).text();
    const stderr = await new Response(process.stderr).text();
    const combined = `${stdout}\n${stderr}`;

    console.log(`\n[Codex Output Log]\n${combined.trim()}\n`);

    const isBlocked = /limit|Upgrade to Pro|try again|rate limit|quota exceeded|usage limit/i.test(combined);
    return !isBlocked && process.exitCode === 0;
};

const runAgyCommand = async (message: string): Promise<boolean> => {
    const process = spawn(["agy", "-m", message], {
        stdin: "pipe",
        stdout: "pipe",
        stderr: "pipe",
    });

    await sleep(1500);

    const UP_ARROW = "\u001b[A";
    const ENTER_KEY = "\r\n";

    try {
        process.stdin.write(UP_ARROW);
        await sleep(150);
        process.stdin.write(UP_ARROW);
        await sleep(150);
        process.stdin.write(ENTER_KEY);
        process.stdin.flush();
        process.stdin.end();
    } catch (err) {
        console.error("Failed to write to agy stdin:", err);
    }

    const stdout = await new Response(process.stdout).text();
    const stderr = await new Response(process.stderr).text();
    const combined = `${stdout}\n${stderr}`;

    console.log(`\n[Agy Output Log]\n${combined.trim()}\n`);

    const isBlocked = /limit|Upgrade to Pro|try again|rate limit|quota exceeded|usage limit/i.test(combined);
    return !isBlocked && process.exitCode === 0;
};

// ==========================================
// RECURSIVE SCHEDULING SYSTEM
// ==========================================

/**
 * Functional tail-recursive retry logic.
 */
const retryWithBackoff = async (
    runner: (msg: string) => Promise<boolean>,
    message: string,
    attempt: number,
    name: string
): Promise<boolean> => {
    try {
        const success = await runner(message);
        if (success) return true;
    } catch (err) {
        console.error(`[${name}] Error on attempt ${attempt}:`, err);
    }

    if (attempt >= CONFIG.maxRetries) {
        return false;
    }

    console.log(`[${name}] Command blocked or failed. Retrying in ${CONFIG.retryDelayMs / 60000}m (Attempt ${attempt}/${CONFIG.maxRetries})...`);
    await sleep(CONFIG.retryDelayMs);
    return retryWithBackoff(runner, message, attempt + 1, name);
};

/**
 * Main recursive execution loop for the task schedulers.
 */
const runWorkerLoop = async (task: TaskConfig, state: WorkerState, lock: Lock): Promise<never> => {
    const delay = state.nextRunTime - Date.now();

    if (delay > 0) {
        console.log(`[${task.name}] Next execution scheduled in ${Math.round(delay / 1000)}s...`);
        await sleep(delay);
    }

    const runStart = Date.now();
    const message = task.getMessage(state.iteration);

    console.log(`[${task.name}] Iteration ${state.iteration} is ready. Acquiring execution lock...`);

    // Exclusive lock block: protects the workspace from concurrent AI modifications
    const success = await lock.runExclusive(async () => {
        console.log(`[${task.name}] Lock acquired. Starting Iteration ${state.iteration}...`);
        return await retryWithBackoff(task.runner, message, 1, task.name);
    });

    if (success) {
        console.log(`[${task.name}] Iteration ${state.iteration} completed successfully. Lock released.`);
    } else {
        console.log(`[${task.name}] Iteration ${state.iteration} failed after all retries. Lock released.`);
    }

    const nextState: WorkerState = {
        nextRunTime: runStart + task.intervalMs,
        iteration: state.iteration + 1,
    };

    return runWorkerLoop(task, nextState, lock);
};

// ==========================================
// ENTRY POINT (IIFE Pattern)
// ==========================================
(() => {
    const lock = makeLock();

    const tasks: readonly TaskConfig[] = [
        {
            name: "Codex Queue",
            getStartTime: getCodexStartTime,
            intervalMs: CONFIG.codexIntervalMs,
            getMessage: () => (CONFIG.codexMessage),
            runner: runCodexCommand(CONFIG.sessionId),
        },
        {
            name: "Gemini Queue (3.1 Pro Low)",
            getStartTime: getGeminiStartTime,
            intervalMs: CONFIG.geminiIntervalMs,
            getMessage: () => CONFIG.geminiMessage,
            runner: runAgyCommand,
        },
    ];

    console.log("Initializing Serialized Schedulers...");

    // Spin up parallel loop handlers with the shared exclusive lock
    tasks.forEach((task) => {
        const initialState: WorkerState = {
            nextRunTime: task.getStartTime().getTime(),
            iteration: 1,
        };

        console.log(`[${task.name}] Target initialized: ${task.getStartTime().toLocaleString()}`);
        runWorkerLoop(task, initialState, lock).catch((err) => {
            console.error(`[${task.name}] Fatal crash:`, err);
        });
    });
})();
