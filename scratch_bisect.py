import subprocess

with open('tests/elab/async_systems_info.lean', 'r') as f:
    lines = f.readlines()

# Split the file by `#eval`
evals = []
current = []
for line in lines:
    if line.startswith('#eval'):
        if current:
            evals.append(current)
        current = [line]
    else:
        current.append(line)
if current:
    evals.append(current)

# Run each #eval block one by one
header = evals[0] if evals and not evals[0][0].startswith('#eval') else []
start_idx = 1 if header else 0

for i, block in enumerate(evals[start_idx:]):
    idx = i + start_idx
    # Construct the file contents
    content = "".join(header) + "".join(block)
    # Write to a temp file
    temp_path = '/tmp/test_eval.lean'
    with open(temp_path, 'w') as tf:
        tf.write(content)
    
    # Run lean
    res = subprocess.run([
        'build/release/stage1/bin/lean',
        '--root=..',
        '-DprintMessageEndPos=true',
        '-Dlinter.all=false',
        '-DElab.inServer=true',
        '-Dcompiler.postponeCompile=false',
        temp_path
    ], capture_output=True)
    
    print(f"Block {idx}: code {res.returncode}")
    if res.returncode != 0:
        print("CRASHED BLOCK:")
        print("".join(block))
        print("STDOUT:", res.stdout.decode('utf-8', errors='ignore'))
        print("STDERR:", res.stderr.decode('utf-8', errors='ignore'))
        break
