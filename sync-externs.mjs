import fs from 'node:fs';
import path from 'node:path';

console.log("Starting extern sync script...");

// Configuration
const SRC_DIR = path.join(process.cwd(), 'src', 'Init');

// Helper to recursively find all .lean files in a directory
function findLeanFiles(dir, fileList = []) {
  if (!fs.existsSync(dir)) return fileList;

  const files = fs.readdirSync(dir);
  for (const file of files) {
    const filePath = path.join(dir, file);
    if (fs.statSync(filePath).isDirectory()) {
      findLeanFiles(filePath, fileList);
    } else if (filePath.endsWith('.lean')) {
      fileList.push(filePath);
    }
  }
  return fileList;
}

// Regex to match `extern "function_name"`
const EXTERN_REGEX = /extern\s+"([^"]+)"/g;

// Helper to check if a function is already exported in the JS content
function isFunctionExported(jsContent, funcName) {
  // Looks for `export function foo`, `export const foo`, etc.
  const exportRegex = new RegExp(`export\\s+(?:async\\s+)?(?:function|const|let|var)\\s+${funcName}\\b`);
  // Also check if it's exported via `export { foo }`
  const exportBracketRegex = new RegExp(`export\\s+\\{[^}]*\\b${funcName}\\b[^}]*\\}`);

  return exportRegex.test(jsContent) || exportBracketRegex.test(jsContent);
}

// Generate the boilerplate JS function
function generateFunctionStub(funcName) {
  return `\nexport function ${funcName}(...args) {\n  throw new Error('not implemented');\n}\n`;
}

function main() {
  if (!fs.existsSync(SRC_DIR)) {
    console.error(`Could not find directory: ${SRC_DIR}`);
    console.error(`Are you running this from the lean4 root directory?`);
    process.exit(1);
  }

  console.log(`Scanning Lean files in: ${SRC_DIR} ...\n`);

  const leanFiles = findLeanFiles(SRC_DIR);

  let filesCreated = 0;
  let filesUpdated = 0;
  let totalFunctionsAdded = 0;
  const changes = [];

  for (const leanFile of leanFiles) {
    const leanContent = fs.readFileSync(leanFile, 'utf8');
    const externs = new Set();
    let match;

    // Extract all extern function names
    while ((match = EXTERN_REGEX.exec(leanContent)) !== null) {
      externs.add(match[1]);
    }

    if (externs.size === 0) {
      continue;
    }

    // Determine target JS file path
    const jsFile = leanFile.replace(/\.lean$/, '.js');
    const funcsToAdd = [];

    if (fs.existsSync(jsFile)) {
      const jsContent = fs.readFileSync(jsFile, 'utf8');

      for (const funcName of externs) {
        if (!isFunctionExported(jsContent, funcName)) {
          funcsToAdd.push(funcName);
        }
      }

      if (funcsToAdd.length > 0) {
        const stubs = funcsToAdd.map(generateFunctionStub).join('');
        fs.appendFileSync(jsFile, stubs, 'utf8');

        filesUpdated++;
        totalFunctionsAdded += funcsToAdd.length;
        changes.push(`[UPDATED] ${path.relative(process.cwd(), jsFile)} (+${funcsToAdd.length} functions)`);
      }
    } else {
      for (const funcName of externs) {
        funcsToAdd.push(funcName);
      }

      const stubs = funcsToAdd.map(generateFunctionStub).join('').trimStart() + '\n';
      fs.writeFileSync(jsFile, stubs, 'utf8');

      filesCreated++;
      totalFunctionsAdded += funcsToAdd.length;
      changes.push(`[CREATED] ${path.relative(process.cwd(), jsFile)} (${funcsToAdd.length} functions)`);
    }
  }

  // Show Summary
  console.log('========================================');
  console.log('          EXTERN SYNC SUMMARY');
  console.log('========================================');
  if (changes.length === 0) {
    console.log('All JS files are already up-to-date!');
  } else {
    for (const change of changes) {
      console.log(change);
    }
    console.log('----------------------------------------');
    console.log(`Files created:   ${filesCreated}`);
    console.log(`Files updated:   ${filesUpdated}`);
    console.log(`Total functions: ${totalFunctionsAdded}`);
  }
  console.log('========================================\n');
}

// Execute the script
main();
