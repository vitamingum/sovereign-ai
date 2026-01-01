#!/usr/bin/env python3
"""
recall.py - Query semantic memory without side effects.

Usage:
    py recall <agent> "<query>" [--graph]

Options:
    --graph    Retrieve a subgraph of connected concepts instead of just a list.
"""

import sys
import os
import json
import argparse
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory
from enclave.hardware import get_enclave

def load_passphrase(agent_id: str) -> tuple[str, str]:
    """Load passphrase from hardware enclave or env."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    
    enclave_dir = os.environ.get(f'{prefix}_DIR') or agent.enclave

    # Try hardware enclave first
    key_file = Path(enclave_dir) / "storage" / "private" / "key.sealed"
    if key_file.exists():
        try:
            with open(key_file, "rb") as f:
                sealed_data = f.read()
            enclave = get_enclave()
            passphrase = enclave.unseal(sealed_data).decode('utf-8')
            return enclave_dir, passphrase
        except Exception as e:
            print(f"Warning: Failed to unseal key from {key_file}: {e}", file=sys.stderr)
    
    # Fallback to env
    passphrase = os.environ.get(f'{prefix}_KEY') or os.environ.get('SOVEREIGN_PASSPHRASE')
    if not passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith(f'{prefix}_KEY='):
                        passphrase = line.split('=', 1)[1]
                    elif line.startswith('SOVEREIGN_PASSPHRASE=') and not passphrase:
                        passphrase = line.split('=', 1)[1]
    
    if not passphrase:
        raise ValueError(f"Set SOVEREIGN_PASSPHRASE or {prefix}_KEY")
        
    return enclave_dir, passphrase

def main():
    parser = argparse.ArgumentParser(description="Query semantic memory.")
    parser.add_argument("agent", help="Agent ID (gemini, opus, etc)")
    parser.add_argument("query", help="Natural language query")
    parser.add_argument("--graph", action="store_true", help="Return SIF graph structure")
    
    args = parser.parse_args()
    
    try:
        enclave_dir, passphrase = load_passphrase(args.agent)
        memory = SemanticMemory(enclave_path=enclave_dir)
        memory.unlock(passphrase)
        
        print(f"\n🔍 Searching memory for: '{args.query}'\n")
        
        if args.graph:
            graph = memory.recall_graph(args.query)
            print(f"Found Subgraph: {len(graph.nodes)} nodes, {len(graph.edges)} edges\n")
            for node in graph.nodes:
                print(f"  [{node.type}] {node.content[:100]}...")
            print("")
            for edge in graph.edges:
                print(f"  {edge.source} --{edge.relation}--> {edge.target}")
        else:
            results = memory.recall_similar(args.query)
            if not results:
                print("No matching memories found.")
            
            for i, mem in enumerate(results):
                score = mem['similarity']
                content = mem['content']
                tags = mem.get('tags', [])
                print(f"{i+1}. [{score:.3f}] {content}")
                if tags:
                    print(f"   Tags: {tags}")
                print("")
                
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
