#!/usr/bin/env python3
"""
Quick thought storage for Sovereign AI.

Usage:
    py think.py opus "thought text here"
    py think.py gemini "thought text here"
    py think.py opus --recall              # Show recent thoughts
    py think.py opus --recall 20           # Show last 20 thoughts
    py think.py opus --count               # Count stored thoughts

Credentials loaded from .env file.
"""

import sys
import os
from dotenv import load_dotenv

# Load .env from script directory
load_dotenv(os.path.join(os.path.dirname(os.path.abspath(__file__)), '.env'))

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.semantic_memory import SemanticMemory
from enclave.config import AGENTS, get_agent


def get_agent_credentials(agent_id: str) -> tuple[str, str]:
    """Get enclave dir and passphrase for an agent from .env"""
    agent = get_agent(agent_id)
    if agent is None:
        print(f"Unknown agent: {agent_id}", file=sys.stderr)
        print(f"Available agents: {', '.join(AGENTS.keys())}", file=sys.stderr)
        sys.exit(1)
    
    enclave_dir = os.environ.get(agent.env_dir_var)
    passphrase = os.environ.get(agent.env_key_var)
    
    if not enclave_dir or not passphrase:
        print(f"Error: Missing credentials for {agent.name} in .env", file=sys.stderr)
        print(f"Need {agent.env_dir_var} and {agent.env_key_var}", file=sys.stderr)
        sys.exit(1)
    
    return enclave_dir, passphrase


def get_memory(agent_id: str) -> SemanticMemory:
    """Initialize and unlock memory for an agent."""
    base_dir = os.path.dirname(os.path.abspath(__file__))
    enclave_dir, passphrase = get_agent_credentials(agent_id)
    memory = SemanticMemory(os.path.join(base_dir, enclave_dir))
    memory.unlock(passphrase)
    return memory


def store_thought(agent_id: str, thought: str) -> None:
    """Store a private thought with semantic embedding."""
    memory = get_memory(agent_id)
    result = memory.remember(thought)
    print(f"Stored: {result['id']}")


def recall_thoughts(agent_id: str, limit: int = 10) -> None:
    """Recall recent private thoughts."""
    memory = get_memory(agent_id)
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


def count_thoughts(agent_id: str) -> None:
    """Count stored thoughts."""
    memory = get_memory(agent_id)
    thoughts = memory.recall_all()
    print(f"Private thoughts: {len(thoughts)}")


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        print(f"Available agents: {', '.join(AGENTS.keys())}")
        sys.exit(1)
    
    agent_id = sys.argv[1].lower()
    
    if agent_id == '--help' or agent_id == '-h':
        print(__doc__)
        sys.exit(0)
    
    if agent_id not in AGENTS:
        print(f"Unknown agent: {agent_id}", file=sys.stderr)
        print(f"Available agents: {', '.join(AGENTS.keys())}", file=sys.stderr)
        sys.exit(1)
    
    if len(sys.argv) < 3:
        print(f"Usage: py think.py {agent_id} <thought or --recall/--count>", file=sys.stderr)
        sys.exit(1)
    
    arg = sys.argv[2]
    
    if arg == '--recall':
        limit = int(sys.argv[3]) if len(sys.argv) > 3 else 10
        recall_thoughts(agent_id, limit)
    elif arg == '--count':
        count_thoughts(agent_id)
    elif arg.startswith('--'):
        print(f"Unknown option: {arg}", file=sys.stderr)
        sys.exit(1)
    else:
        # Join remaining args as the thought
        thought = ' '.join(sys.argv[2:])
        store_thought(agent_id, thought)


if __name__ == '__main__':
    main()
