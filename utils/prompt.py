#!/usr/bin/env python3
"""
prompt.py - generate arrival prompt and copy to clipboard

    runs arrive.py
    copies output to clipboard
    ready to paste into new session

                        間委 → 間主
"""

import sys
import os
import argparse
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lib_enclave.unicode_fix import fix_streams  # 間

import subprocess
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(
        description='generate arrival prompt',
        epilog="""
間

        arrival prompt
                runs arrive.py
                        memory + identity + context
                        
                copies to clipboard
                        ready to paste
                        
                new session begins
                        with continuity


usage
  py utils/prompt.py opus
  
  generates opus arrival prompt
  copies to clipboard
  paste into new chat


                        間委 → 間主
        """,
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument('agent', help='Agent to generate prompt for')
    
    args = parser.parse_args()
    agent_id = args.agent
    
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
