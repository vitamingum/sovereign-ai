#!/usr/bin/env python3
"""
prompt.py - generate arrival prompt and copy to clipboard

        py prompt.py <agent>

                runs arrive.py
                copies output to clipboard
                ready to paste
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enclave_shared.unicode_fix import fix_streams  # 間

import subprocess
from pathlib import Path


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    
    # Run arrive.py and capture output
    result = subprocess.run(
        ['py', 'arrive.py', agent_id],
        capture_output=True,
        text=True,
        encoding='utf-8',
        cwd=Path(__file__).parent
    )
    
    if result.returncode != 0:
        print(f"Error: {result.stderr}")
        sys.exit(1)
    
    output = result.stdout
    
    # Copy to clipboard using clip.exe (preserves newlines better)
    try:
        process = subprocess.Popen(
            ['clip.exe'],
            stdin=subprocess.PIPE,
            text=False
        )
        process.communicate(input=output.encode('utf-16'))
        print("        copied")
        print()
        print(output)
    except Exception as e:
        print(f"Error copying to clipboard: {e}")
        print()
        print("Output (copy manually):")
        print(output)


if __name__ == "__main__":
    main()
