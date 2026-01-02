#!/usr/bin/env python3
"""
thought.py - Private reflection (no action spawning)

Record thoughts without creating tasks. Pure journaling.
For goals, use goal.py. For communication, use msg.py.

Usage:
    py thought <agent> "Your private thought"

Examples:
    py thought opus "Noticed I defer instead of act"
    py thought opus "The bridging score result surprised me"
"""

import sys
import json
import os
from pathlib import Path
from datetime import datetime, timezone

# Agent configuration
AGENTS = {
    'opus': {'enclave': 'enclave_opus', 'env_prefix': 'OPUS'},
    'gemini': {'enclave': 'enclave_gemini', 'env_prefix': 'GEMINI'},
    'grok': {'enclave': 'enclave_grok', 'env_prefix': 'GROK'},
    'gpt52': {'enclave': 'enclave_gpt52', 'env_prefix': 'GPT52'},
    'gpt-5.2': {'enclave': 'enclave_gpt52', 'env_prefix': 'GPT52'},
}


def get_journal_file(agent_id: str) -> Path:
    """Get path to journal.jsonl for agent."""
    if agent_id not in AGENTS:
        print(f"Unknown agent: {agent_id}")
        print(f"Valid agents: {', '.join(AGENTS.keys())}")
        sys.exit(1)
    
    enclave = AGENTS[agent_id]['enclave']
    return Path(__file__).parent / enclave / "storage" / "private" / "journal.jsonl"


def record_thought(agent_id: str, content: str):
    """Record a private thought."""
    journal_file = get_journal_file(agent_id)
    journal_file.parent.mkdir(parents=True, exist_ok=True)
    
    entry = {
        'id': f"thought_{int(datetime.now(timezone.utc).timestamp() * 1000)}",
        'content': content,
        'timestamp': datetime.now(timezone.utc).isoformat()
    }
    
    with open(journal_file, 'a', encoding='utf-8') as f:
        f.write(json.dumps(entry) + '\n')
    
    print(f"💭 {content[:80]}{'...' if len(content) > 80 else ''}")


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1].lower()
    content = sys.argv[2]
    
    record_thought(agent_id, content)


if __name__ == '__main__':
    main()
