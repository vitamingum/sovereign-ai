#!/usr/bin/env python3
"""Quick semantic search for agent memories."""

import sys
import os
from dotenv import load_dotenv

load_dotenv(os.path.join(os.path.dirname(os.path.abspath(__file__)), '.env'))

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.semantic_memory import SemanticMemory
from enclave.config import AGENTS, get_agent_or_raise


def main():
    if len(sys.argv) < 3:
        print("Usage: py recall.py <agent> <query>")
        print(f"Agents: {', '.join(AGENTS.keys())}")
        sys.exit(1)
    
    agent_id = sys.argv[1].lower()
    query = ' '.join(sys.argv[2:])
    
    try:
        agent = get_agent_or_raise(agent_id)
    except ValueError:
        print(f"Unknown agent: {agent_id}")
        sys.exit(1)
    
    enclave_dir = os.environ.get(agent.env_dir_var)
    passphrase = os.environ.get(agent.env_key_var)
    
    if not enclave_dir or not passphrase:
        print(f"Missing credentials for {agent_id}")
        sys.exit(1)
    
    base_dir = os.path.dirname(os.path.abspath(__file__))
    m = SemanticMemory(os.path.join(base_dir, enclave_dir))
    m.unlock(passphrase)
    
    results = m.recall_similar(query, top_k=5)
    
    if not results:
        print("No matching memories found.")
        return
    
    print(f"=== Results for: {query} ===\n")
    for r in results:
        ts = r['timestamp'][:19]
        sim = r['similarity']
        content = r['content']
        print(f"[{ts}] ({sim:.2f})")
        print(content[:500])
        print()


if __name__ == '__main__':
    main()
