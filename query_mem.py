#!/usr/bin/env python3
"""Quick memory query tool."""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.semantic_memory import SemanticMemory

def main():
    # Usage: query_mem.py <agent> <query> [top_k]
    agent = sys.argv[1] if len(sys.argv) > 1 else "opus"
    query = sys.argv[2] if len(sys.argv) > 2 else "failure mode gotcha assumption"
    top_k = int(sys.argv[3]) if len(sys.argv) > 3 else 10
    enclave = f"enclave_{agent}"
    
    sm = SemanticMemory(enclave)
    passphrase = os.environ.get('ENCLAVE_OPUS_KEY', '')
    if not passphrase:
        print("Set ENCLAVE_OPUS_KEY")
        sys.exit(1)
    sm.unlock(passphrase)
    
    print(f"Query: {query}\n")
    results = sm.recall_similar(query, top_k=top_k)
    
    for r in results:
        score = r.get('similarity', 0)
        meta = r.get('metadata', {})
        node_type = meta.get('node_type', '?')
        content = r.get('content', '')
        graph = meta.get('graph_id', '?')
        
        print(f"{score:.2f} [{node_type:15}] {content[:75]}")
        print(f"     graph: {graph}")
        print()

if __name__ == "__main__":
    main()
