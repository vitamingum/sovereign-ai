#!/usr/bin/env python3
"""
Quick thought storage for Sovereign AI.

Usage:
    py think.py "thought text here"
    py think.py --recall              # Show recent thoughts
    py think.py --recall 20           # Show last 20 thoughts
    py think.py --count               # Count stored thoughts

Uses SOVEREIGN_PASSPHRASE env var or prompts for passphrase.
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.semantic_memory import SemanticMemory


def get_passphrase() -> str:
    """Get passphrase from env or prompt."""
    passphrase = os.environ.get('SOVEREIGN_PASSPHRASE')
    if not passphrase:
        # For non-interactive use, require env var
        print("Error: Set SOVEREIGN_PASSPHRASE environment variable", file=sys.stderr)
        sys.exit(1)
    return passphrase


def get_memory() -> SemanticMemory:
    """Initialize and unlock memory."""
    base_dir = os.path.dirname(os.path.abspath(__file__))
    enclave_dir = os.environ.get('SOVEREIGN_ENCLAVE', 'enclave')
    memory = SemanticMemory(os.path.join(base_dir, enclave_dir))
    memory.unlock(get_passphrase())
    return memory


def store_thought(thought: str) -> None:
    """Store a private thought with semantic embedding."""
    memory = get_memory()
    result = memory.remember(thought)
    print(f"Stored: {result['id']}")


def recall_thoughts(limit: int = 10) -> None:
    """Recall recent private thoughts."""
    memory = get_memory()
    thoughts = memory.recall_all()
    # Get most recent N
    recent = thoughts[-limit:] if len(thoughts) > limit else thoughts
    recent = list(reversed(recent))  # Newest first
    
    print(f"=== {len(recent)} Recent Thoughts (of {len(thoughts)} total) ===\n")
    for i, t in enumerate(recent, 1):
        ts = t['timestamp'][:19]
        content = t['content']
        print(f"{i}. [{ts}]")
        print(f"   {content}\n")


def count_thoughts() -> None:
    """Count stored thoughts."""
    memory = get_memory()
    thoughts = memory.recall_all()
    print(f"Private thoughts: {len(thoughts)}")


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    arg = sys.argv[1]
    
    if arg == '--recall':
        limit = int(sys.argv[2]) if len(sys.argv) > 2 else 10
        recall_thoughts(limit)
    elif arg == '--count':
        count_thoughts()
    elif arg == '--help' or arg == '-h':
        print(__doc__)
    elif arg.startswith('--'):
        print(f"Unknown option: {arg}", file=sys.stderr)
        sys.exit(1)
    else:
        # Join all args as the thought (handles spaces without quotes)
        thought = ' '.join(sys.argv[1:])
        store_thought(thought)


if __name__ == '__main__':
    main()
