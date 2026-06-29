import sys, json
from collections import defaultdict

messages = defaultdict(list)

for line in sys.stdin:
    try:
        data = json.loads(line)
        if data.get("reason") == "compiler-message":
            msg = data.get("message", {})
            level = msg.get("level")
            if level in ("error", "warning"):
                code = msg.get("code", {}).get("code", "UNKNOWN") if msg.get("code") else "UNKNOWN"
                rendered = msg.get("rendered", "")
                messages[(level, code)].append(rendered)
    except Exception:
        pass

# Sorting keys puts "error" before "warning" alphabetically
for (level, code), items in sorted(messages.items()):
    label = f"{level.capitalize()} Code: {code}"
    print(f"\n=================== {label} (Showing {min(len(items), 5)} of {len(items)}) ===================")
    for item in items[:5]:
        print(item)
