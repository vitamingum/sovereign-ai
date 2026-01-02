#!/usr/bin/env python3
"""
refresh.py - Prepare context for updating stale understanding.

Usage:
    py refresh <agent> <file>

Outputs side-by-side:
1. OLD: Existing understanding from semantic memory
2. NEW: Current file content

You (the agent) then merge these and call remember.py with updated SIF.
This is the human-in-loop step - you see what changed and decide what matters.
"""

import sys
import os
import subprocess
import hashlib
from pathlib import Path


def get_file_hash(filepath: str) -> str:
    """Get first 12 chars of file hash."""
    with open(filepath, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()[:12]


def recollect(agent: str, filepath: str) -> str:
    """Run recollect and capture output."""
    result = subprocess.run(
        ["python", "recollect.py", agent, filepath],
        capture_output=True,
        text=True,
        cwd=Path(__file__).parent
    )
    return result.stdout + result.stderr


def read_file(filepath: str) -> str:
    """Read file contents."""
    with open(filepath, 'r', encoding='utf-8-sig') as f:
        return f.read()


def main():
    if len(sys.argv) < 3:
        print("Usage: py refresh <agent> <file>")
        print("\nGathers old understanding + current file for you to merge.")
        sys.exit(1)
    
    agent = sys.argv[1]
    filepath = sys.argv[2]
    
    # Resolve filepath
    if not os.path.isabs(filepath):
        filepath = os.path.join(os.getcwd(), filepath)
    
    if not os.path.exists(filepath):
        print(f"❌ File not found: {filepath}")
        sys.exit(1)
    
    filename = os.path.basename(filepath)
    current_hash = get_file_hash(filepath)
    
    print(f"🔄 REFRESH: {filename}")
    print(f"   Hash: {current_hash}")
    print("=" * 60)
    
    # Step 1: Recollect
    print("\n📖 EXISTING UNDERSTANDING:")
    print("-" * 60)
    old_understanding = recollect(agent, filepath)
    print(old_understanding)
    
    # Step 2: Read current
    print("\n📄 CURRENT FILE:")
    print("-" * 60)
    current_content = read_file(filepath)
    # Truncate for display if very long
    if len(current_content) > 3000:
        print(current_content[:3000])
        print(f"\n... ({len(current_content) - 3000} more chars, {len(current_content.splitlines())} total lines)")
    else:
        print(current_content)
    
    print("\n" + "=" * 60)
    print("🎯 NOW: Create merged SIF and run:")
    print(f"   py remember {agent} {filename} \"@G ...\"")


if __name__ == "__main__":
    main()
