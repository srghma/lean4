#!/usr/bin/env bun

import fs from "node:fs/promises";
import path from "node:path";

const rootDir = path.resolve(path.join(import.meta.dir, ".."));
const genDir = path.join(rootDir, "src/rust/lean_runtime/src/gen");
const genRsPath = path.join(rootDir, "src/rust/lean_runtime/src/gen.rs");

/**
 * Searches for and uncomments the module declaration in the file content.
 * Returns the modified content and whether the module is inline.
 */
function uncommentAndCheckInline(content: string, comp: string): { updatedContent: string; isInline: boolean } {
  const lines = content.split(/\r?\n/);
  let isInline = false;
  let inlineIndex = -1;
  let indent = "";

  // 1. Try to find inline module declaration: e.g., `pub mod comp {`
  const inlineRegex = new RegExp(`^(\\s*)(?://\\s*)?(pub\\s+mod\\s+${comp}\\s*\\{)`);

  for (let i = 0; i < lines.length; i++) {
    const match = lines[i].match(inlineRegex);
    if (match) {
      inlineIndex = i;
      indent = match[1];
      lines[i] = indent + match[2]; // Uncomment
      isInline = true;
      break;
    }
  }

  if (isInline && inlineIndex !== -1) {
    // Locate and uncomment the corresponding closing brace
    const closeRegex = new RegExp(`^${indent}(?://\\s*)?(\\}\\s*)$`);
    for (let i = inlineIndex + 1; i < lines.length; i++) {
      const match = lines[i].match(closeRegex);
      if (match) {
        lines[i] = indent + match[1]; // Uncomment closing brace
        break;
      }
    }
    return { updatedContent: lines.join("\n"), isInline: true };
  }

  // 2. Try to find external module declaration: e.g., `pub mod comp;`
  const modRegex = new RegExp(`^(\\s*)(?://\\s*)?(pub\\s+mod\\s+${comp}\\s*;)`);
  const pathRegex = new RegExp(`^(\\s*)(?://\\s*)?(\\[path\\s*=.*?\\])`);

  for (let i = 0; i < lines.length; i++) {
    const modMatch = lines[i].match(modRegex);
    if (modMatch) {
      const indent = modMatch[1];
      lines[i] = indent + modMatch[2]; // Uncomment pub mod line

      // Uncomment the preceding #[path] attribute if one exists
      if (i > 0) {
        const pathMatch = lines[i - 1].match(pathRegex);
        if (pathMatch) {
          lines[i - 1] = indent + pathMatch[2];
        }
      }
      break;
    }
  }

  return { updatedContent: lines.join("\n"), isInline: false };
}

async function enableModule(modPath: string) {
  const comps = modPath.split(".");
  if (comps.length === 0) return;

  let currentFilePath = genRsPath;
  let currentDir = genDir;

  for (let i = 0; i < comps.length; i++) {
    const comp = comps[i];

    let content = "";
    try {
      content = await fs.readFile(currentFilePath, "utf8");
    } catch (err) {
      console.error(`Error reading file ${currentFilePath}:`, err);
      return;
    }

    // Uncomment module declaration in the parent file
    const { updatedContent, isInline } = uncommentAndCheckInline(content, comp);
    if (updatedContent !== content) {
      await fs.writeFile(currentFilePath, updatedContent, "utf8");
      console.log(`Uncommented module declaration for '${comp}' in ${path.relative(rootDir, currentFilePath)}`);
    }

    if (isInline) {
      // If it is inline (like pub mod Init { ... }), directory shifts but source file remains the same
      currentDir = path.join(currentDir, comp);
    } else {
      // Find #[path = "..."] if defined to compute the next filename
      const pathAttrRegex = new RegExp(
        `^\\s*(?://\\s*)?\\[path\\s*=\\s*"([^"]+)"\\]\\s*\\r?\\n\\s*(?://\\s*)?pub\\s+mod\\s+${comp}\\b`,
        "m"
      );
      const match = updatedContent.match(pathAttrRegex);

      let resolvedPath: string;
      if (match) {
        const attrPath = match[1];
        if (path.basename(currentFilePath) === "gen.rs") {
          resolvedPath = path.resolve(currentDir, attrPath);
        } else {
          resolvedPath = path.resolve(path.dirname(currentFilePath), attrPath);
        }
      } else {
        resolvedPath = path.join(currentDir, `${comp}.rs`);
      }

      // Check if file exists as .rs or .rs_ and rename if necessary
      const rsExists = await fs.stat(resolvedPath).then(s => s.isFile()).catch(() => false);
      const rsUnderscorePath = resolvedPath + "_";
      const rsUnderscoreExists = await fs.stat(rsUnderscorePath).then(s => s.isFile()).catch(() => false);

      if (rsUnderscoreExists && !rsExists) {
        await fs.rename(rsUnderscorePath, resolvedPath);
        console.log(`Renamed: ${path.relative(rootDir, rsUnderscorePath)} -> ${path.relative(rootDir, resolvedPath)}`);
      }

      // Shift state down to the submodule file
      currentFilePath = resolvedPath;
      currentDir = path.join(currentDir, comp);
    }
  }
}

async function main() {
  const args = process.argv.slice(2);
  if (args.length === 0) {
    console.log("Usage: bun enable_gen_leaf.ts <Module.Path...>");
    process.exit(1);
  }

  for (const mod of args) {
    console.log(`Enabling module: ${mod}`);
    await enableModule(mod);
  }
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
