#!/usr/bin/env python3
import re
from pathlib import Path

SRC_DIR = Path(__file__).parent.parent / "src/rust/lean_runtime/src"

def fix_file(filepath: Path):
    text = filepath.read_text()
    orig = text
    
    # Replace pub use for any module ending in _impl
    # e.g., pub use runtime_tcp_impl::*; -> pub(crate) use runtime_tcp_impl::*;
    text = re.sub(
        r'\bpub\s+use\s+(\w+_impl\b)',
        r'pub(crate) use \1',
        text
    )
    
    if filepath.name == 'lib.rs':
        # In lib.rs, change all pub use of runtime_, kernel_, library_ to pub(crate) use
        text = re.sub(
            r'\bpub\s+use\s+(runtime_|kernel_|library_)',
            r'pub(crate) use \1',
            text
        )
        
    if text != orig:
        filepath.write_text(text)
        print(f"Fixed: {filepath.name}")

def main():
    for f in SRC_DIR.glob('*.rs'):
        fix_file(f)

if __name__ == '__main__':
    main()
