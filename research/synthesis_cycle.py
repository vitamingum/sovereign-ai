#!/usr/bin/env python3
"""
synthesis_cycle.py - Identify and bridge semantic gaps.

1. Loads all semantic memories.
2. Finds the two most dissimilar (distant) concepts.
3. Proposes a synthesis task to bridge them.
"""

import sys
import os
import json
import numpy as np
from pathlib import Path
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from enclave_shared.semantic_memory import SemanticMemory
from wake import load_passphrase

def find_semantic_gap(agent_id: str):
    print(f"Loading memory for {agent_id}...")
    enclave_dir, passphrase = load_passphrase(agent_id)
    memory = SemanticMemory(enclave_path=enclave_dir)
    memory.unlock(passphrase)
    
    # Access private storage directly to get all embeddings
    log_file = Path(enclave_dir) / "storage" / "private" / "semantic_memories.jsonl"
    if not log_file.exists():
        print("No memories found.")
        return

    memories = []
    with open(log_file, 'r', encoding='utf-8') as f:
        for line in f:
            if not line.strip(): continue
            try:
                entry = json.loads(line)
                if "embedding" in entry:
                    # Decrypt embedding
                    emb = memory._decrypt_embedding(entry["embedding"])
                    
                    # Decrypt content for display
                    content_nonce = bytes.fromhex(entry["content_nonce"])
                    content_ciphertext = bytes.fromhex(entry["content"])
                    decrypted_bytes = memory._decrypt(
                        content_nonce, content_ciphertext, memory._encryption_key
                    )
                    try:
                        payload = json.loads(decrypted_bytes.decode())
                        content = payload.get("text", "") if isinstance(payload, dict) else decrypted_bytes.decode()
                    except:
                        content = decrypted_bytes.decode()
                        
                    memories.append({
                        "id": entry["id"],
                        "content": content,
                        "embedding": emb
                    })
            except Exception as e:
                continue
    
    if len(memories) < 2:
        print("Not enough memories to synthesize.")
        return

    print(f"Scanning {len(memories)} memories for maximum semantic tension...")
    
    # Store all pairs with their similarity
    pairs = []
    
    for m1, m2 in combinations(memories, 2):
        # Cosine similarity
        sim = float(np.dot(m1["embedding"], m2["embedding"]))
        pairs.append((sim, m1, m2))
            
    # Sort by similarity (ascending) -> most distant first
    pairs.sort(key=lambda x: x[0])
    
    print(f"\n--- TOP 3 SEMANTIC GAPS ---")
    
    for i, (sim, m1, m2) in enumerate(pairs[:3]):
        tension = 1.0 - sim
        print(f"\nGap #{i+1}: Tension {tension:.4f}")
        print(f"Concept A: {m1['content'][:100]}...")
        print(f"Concept B: {m2['content'][:100]}...")
        
    if pairs:
        # Propose the first one by default, but user can choose
        sim, m1, m2 = pairs[0]
        print("\nProposed Synthesis Task (for Gap #1):")
        print(f"Find the hidden connection between '{m1['content'][:50]}...' and '{m2['content'][:50]}...'")
        
        # Generate the think command
        print("\nRun this command to bridge the gap:")
        cmd = f'python think.py {agent_id} "@G synthesis {agent_id} 2026-01-01; N n1 Concept A; N n2 Concept B; N n3 Insight \'[YOUR SYNTHESIS HERE]\'; E n1 connects_to n3; E n3 connects_to n2" 5'
        print(cmd)

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: py synthesis_cycle.py <agent>")
        sys.exit(1)
    find_semantic_gap(sys.argv[1])
