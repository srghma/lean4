import { readFileSync } from "fs";

async function main() {
    console.log("Checking links in transitive_binary_relations.html...");
    const html = readFileSync("transitive_binary_relations.html", "utf8");
    const linkRegex = /href="(https:\/\/leanprover-community\.github\.io[^"]+)"/g;
    const links = new Set<string>();
    let match;
    while ((match = linkRegex.exec(html)) !== null) {
        links.add(match[1]);
    }

    console.log(`Found ${links.size} unique mathlib links. Testing...`);
    let badCount = 0;
    
    // Test in parallel chunks
    const chunks = Array.from(links);
    const chunkSize = 10;
    for (let i = 0; i < chunks.length; i += chunkSize) {
        const batch = chunks.slice(i, i + chunkSize);
        await Promise.all(batch.map(async (url) => {
            try {
                // If there's an anchor, we must GET the body to check it
                const hashIndex = url.indexOf('#');
                if (hashIndex !== -1) {
                    const baseUrl = url.substring(0, hashIndex);
                    const anchor = url.substring(hashIndex + 1);
                    const res = await fetch(baseUrl, { method: "GET" });
                    if (!res.ok) {
                        console.error(`❌  Dead link [${res.status}]: ${url}`);
                        badCount++;
                    } else {
                        const body = await res.text();
                        // Mathlib docs use id="Anchor" for declarations
                        if (body.includes(`id="${anchor}"`)) {
                            console.log(`✅  OK (Anchor found): ${url}`);
                        } else {
                            console.error(`❌  Anchor not found [${res.status}]: ${url} (Missing id="${anchor}")`);
                            badCount++;
                        }
                    }
                } else {
                    const res = await fetch(url, { method: "HEAD" });
                    if (!res.ok) {
                        console.error(`❌  Dead link [${res.status}]: ${url}`);
                        badCount++;
                    } else {
                        console.log(`✅  OK: ${url}`);
                    }
                }
            } catch (err) {
                console.error(`❌  Error fetching ${url}: ${err.message}`);
                badCount++;
            }
        }));
    }

    if (badCount > 0) {
        console.error(`\nFinished with ${badCount} dead/missing anchor links.`);
        process.exit(1);
    } else {
        console.log("\nAll mathlib links are valid!");
    }
}
main();
