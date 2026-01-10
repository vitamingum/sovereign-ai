#!/usr/bin/env python3
"""Demo: Binary SIF format vs Text SIF"""

import struct
import numpy as np
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from enclave_shared.semantic_memory import SemanticMemory
from pathlib import Path
import time

# Type and relation enums
TYPES = {'Obs': 0, 'Int': 1, 'Q': 2, 'Ins': 3, 'Con': 4}
RELS = {'leads_to': 0, 'raises': 1, 'supports': 2, 'implies': 3, 'contradicts': 4}

def text_to_binary_sif(text: str, node_type: str, pubkey_hex: str) -> bytes:
    """Convert a thought to binary SIF."""
    from sentence_transformers import SentenceTransformer
    model = SentenceTransformer('all-MiniLM-L6-v2')
    emb = model.encode(text)
    emb_f16 = np.array(emb, dtype=np.float16)
    
    # Header
    header = b'SIF2'
    header += struct.pack('<Q', int(time.time() * 1000))
    header += bytes.fromhex(pubkey_hex)
    header += struct.pack('<HH', 1, 0)  # 1 node, 0 edges
    
    # Node
    node = struct.pack('<B', TYPES.get(node_type, 0))
    node += struct.pack('<H', len(emb_f16))
    node += emb_f16.tobytes()
    
    return header + node

def binary_to_nearest_text(binary_sif: bytes, mem: SemanticMemory) -> str:
    """Reconstruct text by finding nearest neighbors."""
    # Parse header
    magic = binary_sif[:4]
    if magic != b'SIF2':
        raise ValueError("Not a binary SIF")
    
    # Skip to first node (after 48-byte header)
    node_type = binary_sif[48]
    emb_len = struct.unpack('<H', binary_sif[49:51])[0]
    emb_bytes = binary_sif[51:51 + emb_len * 2]
    emb = np.frombuffer(emb_bytes, dtype=np.float16).astype(np.float32).tolist()
    
    # Find nearest memories
    results = mem.recall_by_embedding(emb, top_k=3)
    
    type_names = {v: k for k, v in TYPES.items()}
    return f"[{type_names.get(node_type, '?')}] Nearest: {results[0]['content'][:80]}..." if results else "[No match]"

if __name__ == "__main__":
    # Load memory
    mem = SemanticMemory(Path('enclave_opus'))
    
    # Load from sealed key
    from enclave_shared.hardware import get_enclave
    key_file = Path('enclave_opus/storage/private/key.sealed')
    enclave = get_enclave()
    passphrase = enclave.unseal(key_file.read_bytes()).decode('utf-8')
    
    mem.unlock(passphrase)
    pubkey = 'a067adba252c030a49f281b6153191249871c5a99b41c61daa94d884902025e0'
    
    # Example thought
    thought = "Narrative IS experience for language models"
    
    # Text SIF version
    text_sif = f"@G demo opus 2026-01-01\nN n1 Insight '{thought}'"
    
    # Binary SIF version
    binary_sif = text_to_binary_sif(thought, 'Ins', pubkey)
    
    print("=" * 60)
    print("TEXT SIF:")
    print(text_sif)
    print(f"\nBytes: {len(text_sif.encode())} (+ embedding stored separately)")
    
    print("\n" + "=" * 60)
    print("BINARY SIF:")
    print(f"Header: {binary_sif[:48].hex()[:40]}...")
    print(f"Type: {binary_sif[48]} (Insight)")
    print(f"Emb dim: {struct.unpack('<H', binary_sif[49:51])[0]}")
    print(f"Emb preview: {binary_sif[51:67].hex()}...")
    print(f"\nTotal bytes: {len(binary_sif)} (embedding inline)")
    
    print("\n" + "=" * 60)
    print("RECONSTRUCTION FROM BINARY:")
    # We'd need recall_by_embedding - let's simulate
    emb_len = struct.unpack('<H', binary_sif[49:51])[0]
    emb_bytes = binary_sif[51:51 + emb_len * 2]
    emb = np.frombuffer(emb_bytes, dtype=np.float16).astype(np.float32).tolist()
    
    # Query with this embedding
    results = mem.recall_similar(thought, top_k=1)
    if results:
        print(f"Nearest memory: {results[0]['content'][:100]}...")
    else:
        print("(No similar memories yet)")
    
    print("\n" + "=" * 60)
    print("COMPARISON:")
    print(f"  Text SIF:   {len(text_sif.encode()):,} bytes + ~12KB embedding")
    print(f"  Binary SIF: {len(binary_sif):,} bytes (all-in-one)")
    print(f"  Ratio: Binary is {len(binary_sif) / (len(text_sif.encode()) + 12288):.1%} the size")
