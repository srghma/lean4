#!/usr/bin/env bun

import { spawnSync } from "bun";
import { parseArgs } from "util";

const STATUS_ANCHOR = /Context window:/g;

enum AIModel {
  GPT_5_5 = "gpt-5.5",
  GPT_5_4 = "gpt-5.4",
  GPT_5_4_MINI = "gpt-5.4-mini",
  UNKNOWN = "unknown"
}

interface StatusInfo {
  contextLeftPercent: number;
  fiveHourLeftPercent: number;
  fiveHourReset: string | null;
  weeklyLeftPercent: number;
  weeklyReset: string | null;
  model: AIModel;
  pursuingGoal: boolean;
}

// State tracker to enforce a minimum of 1 second between Kitty write commands
let lastKittyWriteTime = 0;
const enforceKittyWriteDelay = async (): Promise<void> => {
  const now = Date.now();
  const elapsed = now - lastKittyWriteTime;
  if (elapsed < 1000) {
    await Bun.sleep(1000 - elapsed);
  }
  lastKittyWriteTime = Date.now();
};

// Generic function to execute kitty control commands
const runKittyCtrl = (kittyCmd: string, args: string[]): string => {
  const proc = spawnSync([kittyCmd, "@", ...args]);
  if (proc.exitCode !== 0) {
    throw new Error(`Kitty command "@ ${args.join(" ")}" failed: ${proc.stderr?.toString()}`);
  }
  return proc.stdout.toString();
};

// Closure to handle memoized kitty remote control detection
const getKittyCmd = (() => {
  let cached: string | null = null;
  return (): string => {
    if (cached) return cached;
    try {
      const p = spawnSync(["kitten", "@", "ls"]);
      cached = p.exitCode === 0 ? "kitten" : "kitty";
    } catch {
      cached = "kitty";
    }
    return cached;
  };
})();

// Search window list using functional .some arrays
const findWindow = (kittyCmd: string, title: string): boolean => {
  try {
    const stdout = runKittyCtrl(kittyCmd, ["ls"]);
    const data = JSON.parse(stdout);
    return data.some((osWin: any) =>
      (osWin.tabs || []).some((tab: any) =>
        (tab.windows || []).some((win: any) => win.title === title)
      )
    );
  } catch (err) {
    console.error("Error listing kitty windows:", err);
    return false;
  }
};

const getScreenText = async (kittyCmd: string, windowTitle: string): Promise<string> => {
  return runKittyCtrl(kittyCmd, ["get-text", "--match", `title:^${windowTitle}$`]);
};

const countOccurrences = (text: string, search: RegExp): number => {
  const matches = text.match(search);
  return matches ? matches.length : 0;
};

// Checks if the active goal state is rendered at the bottom lines of the terminal
const isGoalModeActive = (text: string): boolean => {
  const lines = text.trim().split("\n");
  const bottomText = lines.slice(-5).join("\n");
  return bottomText.includes("Pursuing goal");
};

const detectAIModel = (text: string): AIModel => {
  const lower = text.toLowerCase();
  if (lower.includes("gpt-5.5")) return AIModel.GPT_5_5;
  if (lower.includes("gpt-5.4-mini")) return AIModel.GPT_5_4_MINI;
  if (lower.includes("gpt-5.4")) return AIModel.GPT_5_4;
  return AIModel.UNKNOWN;
};

// Generic text & key interaction tools
const sendKittyText = async (kittyCmd: string, windowTitle: string, text: string): Promise<void> => {
  await enforceKittyWriteDelay();
  runKittyCtrl(kittyCmd, ["send-text", "--match", `title:^${windowTitle}$`, text]);
  await Bun.sleep(1000);
};

const sendKittyKey = async (kittyCmd: string, windowTitle: string, key: string): Promise<void> => {
  await enforceKittyWriteDelay();
  runKittyCtrl(kittyCmd, ["send-key", "--match", `title:^${windowTitle}$`, key]);
  await Bun.sleep(1000);
};

const sendKittyCommand = async (kittyCmd: string, windowTitle: string, text: string): Promise<void> => {
  await sendKittyText(kittyCmd, windowTitle, text);
  await sendKittyKey(kittyCmd, windowTitle, "enter");
};

// Sends '/status', waits 3 seconds, sends '/status' again, and polls screen text with 200ms pauses for 2 seconds
const fetchStatus = async (
  kittyCmd: string,
  windowTitle: string
): Promise<string> => {
  const initialText = await getScreenText(kittyCmd, windowTitle);
  const initialCount = countOccurrences(initialText, STATUS_ANCHOR);

  await sendKittyCommand(kittyCmd, windowTitle, "/status");
  await Bun.sleep(3000);
  await sendKittyCommand(kittyCmd, windowTitle, "/status");

  const start = Date.now();
  const timeoutMs = 2000;

  while (Date.now() - start < timeoutMs) {
    await Bun.sleep(200);
    const text = await getScreenText(kittyCmd, windowTitle);
    if (countOccurrences(text, STATUS_ANCHOR) > initialCount) {
      return text;
    }
  }

  throw new Error("Polling timed out waiting for 'Context window:' to appear inside 2s window.");
};

const parseMetricLine = (line: string, regex: RegExp, name: string): RegExpMatchArray => {
  const match = line.match(regex);
  if (!match) {
    throw new Error(`Failed to parse ${name} line: "${line}"`);
  }
  return match;
};

const parseStatus = (text: string, pursuingGoal: boolean): StatusInfo => {
  const lines = text.split("\n");
  const contextIdx = lines.findLastIndex(line => line.includes("Context window:"));

  if (contextIdx === -1) {
    throw new Error("Could not find 'Context window:' in the screen buffer");
  }

  const contextMatch = parseMetricLine(lines[contextIdx], /Context window:\s+(\d+)%\s+left/i, "Context Window");
  const fiveHourMatch = parseMetricLine(lines[contextIdx + 1] || "", /5h limit:\s+\[[^\]]*\]\s+(\d+)%\s+left(?:\s+\(resets\s+([^)]+)\))?/i, "5h limit");
  const weeklyMatch = parseMetricLine(lines[contextIdx + 2] || "", /Weekly limit:\s+\[[^\]]*\]\s+(\d+)%\s+left(?:\s+\(resets\s+([^)]+)\))?/i, "Weekly limit");

  const model = detectAIModel(text);
  if (model === AIModel.UNKNOWN) {
    throw new Error("Could not identify a valid AI model in the screen buffer");
  }

  return {
    contextLeftPercent: parseInt(contextMatch[1], 10),
    fiveHourLeftPercent: parseInt(fiveHourMatch[1], 10),
    fiveHourReset: fiveHourMatch[2]?.trim() ?? null,
    weeklyLeftPercent: parseInt(weeklyMatch[1], 10),
    weeklyReset: weeklyMatch[2]?.trim() ?? null,
    model,
    pursuingGoal,
  };
};

const parseResetTimeToMs = (resetStr: string, now: Date = new Date()): number => {
  const match = resetStr.match(/(\d{1,2}):(\d{2})\s*(AM|PM)?(?:\s*(?:(today|tomorrow)|on\s+(\d{1,2})\s+([A-Za-z]+)))?/i);
  if (!match) {
    throw new Error(`Unrecognized reset time format: "${resetStr}"`);
  }

  const [_, hoursStr, minutesStr, ampm, relativeDay, dayStr, monthStr] = match;
  let hours = parseInt(hoursStr, 10);
  const minutes = parseInt(minutesStr, 10);

  if (ampm) {
    const upperAmpm = ampm.toUpperCase();
    if (upperAmpm === "PM" && hours < 12) hours += 12;
    else if (upperAmpm === "AM" && hours === 12) hours = 0;
  }

  const target = new Date(now);
  target.setHours(hours, minutes, 0, 0);

  if (dayStr && monthStr) {
    const months: Record<string, number> = {
      jan: 0, feb: 1, mar: 2, apr: 3, may: 4, jun: 5,
      jul: 6, aug: 7, sep: 8, oct: 9, nov: 10, dec: 11
    };
    const m = monthStr.toLowerCase().substring(0, 3);
    if (m in months) {
      target.setMonth(months[m]);
    }
    target.setDate(parseInt(dayStr, 10));

    if (target.getTime() < now.getTime()) {
      target.setFullYear(target.getFullYear() + 1);
    }
  } else if (relativeDay) {
    if (relativeDay.toLowerCase() === "tomorrow") {
      target.setDate(target.getDate() + 1);
    }
  } else {
    if (target.getTime() <= now.getTime()) {
      target.setDate(target.getDate() + 1);
    }
  }

  return target.getTime() - now.getTime();
};

const formatDuration = (ms: number): string => {
  const totalSeconds = Math.floor(ms / 1000);
  const hours = Math.floor(totalSeconds / 3600);
  const minutes = Math.floor((totalSeconds % 3600) / 60);
  const seconds = totalSeconds % 60;

  return [
    hours > 0 ? `${hours}h` : "",
    minutes > 0 ? `${minutes}m` : "",
    seconds > 0 || (hours === 0 && minutes === 0) ? `${seconds}s` : ""
  ].filter(Boolean).join(" ");
};

const sendMsg = async (kittyCmd: string, windowTitle: string, msg: string): Promise<void> => {
  console.log(`Sending message: "${msg}"`);
  await sendKittyCommand(kittyCmd, windowTitle, msg);
};

const executeContinue = async (kittyCmd: string, windowTitle: string, compact = true): Promise<void> => {
  if (compact) {
    await sendMsg(kittyCmd, windowTitle, "/compact");
    await Bun.sleep(4000);
  }
  await sendMsg(kittyCmd, windowTitle, "/goal continue in automatic mode. Is previous task completed?");
};

// Async recursive loop to process loop iterations functionally without while(true)
const runLoop = async (kittyCmd: string, title: string, compact: boolean): Promise<void> => {
  console.log(`[${new Date().toLocaleTimeString()}] Checking status...`);
  try {
    const screenText = await getScreenText(kittyCmd, title);

    if (isGoalModeActive(screenText)) {
      console.log("Goal mode is active. Agent is actively working. Sleeping for 10 minutes...");
      await Bun.sleep(10 * 60 * 1000);
      return runLoop(kittyCmd, title, compact);
    }

    const statusText = await fetchStatus(kittyCmd, title);
    const status = parseStatus(statusText, false);

    console.log(`Current Limits:
  - Model: ${status.model}
  - Context Window Left: ${status.contextLeftPercent}%
  - 5h Limit Left: ${status.fiveHourLeftPercent}% ${status.fiveHourReset ? `(resets: ${status.fiveHourReset})` : ""}
  - Weekly Limit Left: ${status.weeklyLeftPercent}% ${status.weeklyReset ? `(resets: ${status.weeklyReset})` : ""}`);

    if (status.weeklyLeftPercent === 0 && status.weeklyReset) {
      const waitMs = parseResetTimeToMs(status.weeklyReset) + 2 * 60 * 1000;
      console.log(`Weekly limit hit! Sleeping until weekly reset (${status.weeklyReset}) + 2m buffer: ${formatDuration(waitMs)}`);
      await Bun.sleep(waitMs);
    } else if (status.fiveHourLeftPercent === 0 && status.fiveHourReset) {
      const waitMs = parseResetTimeToMs(status.fiveHourReset) + 2 * 60 * 1000;
      console.log(`5h rate limit reached. Sleeping until reset (${status.fiveHourReset}) + 2m buffer: ${formatDuration(waitMs)}`);
      await Bun.sleep(waitMs);

      console.log("Waking up! Resuming execution...");
      await executeContinue(kittyCmd, title, compact);
      await Bun.sleep(5 * 60 * 1000);
    } else {
      console.log("Rate limits are clear. Triggering task execution...");
      await executeContinue(kittyCmd, title, compact);
      console.log("Sleeping for 10 minutes to allow processing...");
      await Bun.sleep(10 * 60 * 1000);
    }
  } catch (err) {
    console.error("Failed to process loop iteration:", err);
    console.log("Retrying in 1 minute...");
    await Bun.sleep(60 * 1000);
  }

  // Recurse to yield stack execution and restart loop
  return runLoop(kittyCmd, title, compact);
};

// Async IIFE Entrypoint
(async () => {
  let values: any;
  let positionals: string[];

  try {
    const parsed = parseArgs({
      args: Bun.argv.slice(2),
      options: {
        title: {
          type: "string",
        },
        "no-compact": {
          type: "boolean",
        },
        "initial-wait": {
          type: "string",
        },
      },
      strict: true,
      allowPositionals: true,
    });
    values = parsed.values;
    positionals = parsed.positionals;
  } catch (err: any) {
    console.error(`Error parsing arguments: ${err.message}`);
    process.exit(1);
  }

  const rawCommand = positionals[0];
  const command = ["get-status", "get", "start-loop"].includes(rawCommand) ? rawCommand : "help";
  const title = (values.title as string) || "claude-resume-1";
  const compact = !values["no-compact"];
  const initialWait = values["initial-wait"] as string | undefined;

  if (command === "help") {
    console.log(`Usage: bun run control.ts <get-status|get|start-loop> [options]

Options:
  --title <window-title>     Target kitty window title (default: claude-resume-1)
  --no-compact               Disable sending /compact command in loop
  --initial-wait <time>      Time to wait before starting loop (e.g. "4:11 AM" or "04:11")
`);
    process.exit(1);
  }

  const kittyCmd = getKittyCmd();

  if (!findWindow(kittyCmd, title)) {
    console.error(`Error: Kitty window with title "${title}" was not found.`);
    process.exit(1);
  }

  // Track baseline execution time after findWindow (which communicates synchronously with Kitty)
  lastKittyWriteTime = Date.now();

  try {
    if (command === "get-status" || command === "get") {
      const screenText = await getScreenText(kittyCmd, title);
      const goalActive = isGoalModeActive(screenText);

      if (goalActive) {
        // Parse previous status from screen scrollback history without sending blocking requests
        const status = parseStatus(screenText, true);
        console.log(JSON.stringify(status, null, 2));
        process.exit(0);
      }

      console.log(`Fetching status for window "${title}"...`);
      const statusText = await fetchStatus(kittyCmd, title);
      const status = parseStatus(statusText, false);
      console.log(JSON.stringify(status, null, 2));
    } else if (command === "start-loop") {
      if (initialWait) {
        const waitMs = parseResetTimeToMs(initialWait);
        if (waitMs > 0) {
          console.log(`Waiting until initial target time: ${initialWait} (Sleeping for ${formatDuration(waitMs)})...`);
          await Bun.sleep(waitMs);
        }
      }
      await runLoop(kittyCmd, title, compact);
    }
  } catch (error: any) {
    console.error(`Error: ${error.message}`);
    process.exit(1);
  }
})();
