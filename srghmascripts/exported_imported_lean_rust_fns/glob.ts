import path from "node:path";

const normalizePathForGlob = (input: string) => input.replaceAll(path.sep, "/");

export const globToRegExp = (globPattern: string): RegExp => {
    let regex = "^";
    for (let i = 0; i < globPattern.length; i++) {
        const char = globPattern[i]!;
        const nextChar = globPattern[i + 1] || "";

        if (char === "*") {
            if (nextChar === "*") {
                const afterNext = globPattern[i + 2] || "";
                if (afterNext === "/") {
                    regex += "(?:.*/)?";
                    i += 2;
                } else {
                    regex += ".*";
                    i += 1;
                }
            } else {
                regex += "[^/]*";
            }
        } else if (char === "?") {
            regex += "[^/]";
        } else if ("\\.[]{}()+-^$|".includes(char)) {
            regex += `\\${char}`;
        } else {
            regex += char;
        }
    }
    regex += "$";
    return new RegExp(regex);
};

export const makePathExcluder = (cwd: string, rootDir: string, ignoredPathGlobs: string[]) => {
    const ignoredMatchers = ignoredPathGlobs.map(globToRegExp);

    return (entry: string) => {
        const absolutePath = path.isAbsolute(entry) ? entry : path.resolve(cwd, entry);
        const repoRelativePath = normalizePathForGlob(path.relative(rootDir, absolutePath));
        return ignoredMatchers.some((matcher) => matcher.test(repoRelativePath));
    };
};
