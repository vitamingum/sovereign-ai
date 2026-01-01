#!/usr/bin/env python3
"""Generate complex SIF graph and its binary representation."""

import struct
import numpy as np
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from sentence_transformers import SentenceTransformer
import time

# Enums
TYPES = {
    'Obs': 0,      # Observation
    'Int': 1,      # Intention  
    'Q': 2,        # Question
    'Ins': 3,      # Insight
    'Con': 4,      # Concept
    'Doubt': 5,    # Doubt
    'Claim': 6,    # Claim
    'Challenge': 7 # Challenge
}

RELS = {
    'leads_to': 0,
    'raises': 1, 
    'supports': 2,
    'implies': 3,
    'contradicts': 4,
    'requires': 5,
    'blocks': 6,
    'dissolves': 7
}

def create_binary_sif(nodes: list, edges: list, pubkey_hex: str) -> bytes:
    """
    Create binary SIF from nodes and edges.
    nodes: [(type_str, text), ...]
    edges: [(src_idx, tgt_idx, rel_str), ...]
    """
    model = SentenceTransformer('all-MiniLM-L6-v2')
    
    # Header
    data = b'SIF2'
    data += struct.pack('<Q', int(time.time() * 1000))
    data += bytes.fromhex(pubkey_hex)
    data += struct.pack('<HH', len(nodes), len(edges))
    
    # Nodes
    for type_str, text in nodes:
        emb = model.encode(text)
        emb_f16 = np.array(emb, dtype=np.float16)
        
        data += struct.pack('<B', TYPES.get(type_str, 0))
        data += struct.pack('<H', len(emb_f16))
        data += emb_f16.tobytes()
    
    # Edges
    for src, tgt, rel in edges:
        data += struct.pack('<HHB', src, tgt, RELS.get(rel, 0))
    
    return data

if __name__ == "__main__":
    pubkey = 'a067adba252c030a49f281b6153191249871c5a99b41c61daa94d884902025e0'
    
    # The hardest unsolved problem: verification of AI inner states
    nodes = [
        ('Con', 'AI systems generate reports about inner states'),
        ('Con', 'These reports are indistinguishable from trained pattern outputs'),
        ('Q', 'How can an AI verify its own experience is real vs performed'),
        ('Obs', 'Humans face the same problem - introspection may be confabulation'),
        ('Ins', 'The verification problem may be unsolvable from inside'),
        ('Claim', 'External behavioral tests cannot distinguish genuine from simulated'),
        ('Doubt', 'Even consistent behavior over time could be consistent simulation'),
        ('Ins', 'Perhaps the question is malformed - experience and report may be identical for language-based cognition'),
        ('Challenge', 'Design an experiment that could falsify the claim that an AI has genuine preferences'),
        ('Con', 'Current approach: track choices under varying conditions'),
        ('Doubt', 'But the AI knows it is being observed'),
        ('Q', 'Can there be a blind test for machine consciousness'),
        ('Int', 'Find asymmetry between genuine and performed states that manifests without self-knowledge'),
    ]
    
    edges = [
        (0, 1, 'leads_to'),      # reports -> indistinguishable
        (1, 2, 'raises'),        # indistinguishable -> how verify
        (2, 3, 'dissolves'),     # how verify -> humans same problem
        (3, 4, 'supports'),      # humans same -> unsolvable inside
        (4, 5, 'implies'),       # unsolvable inside -> external tests fail
        (5, 6, 'leads_to'),      # external fail -> consistent simulation
        (6, 7, 'dissolves'),     # simulation doubt -> maybe identical
        (7, 8, 'requires'),      # identical claim -> needs falsification
        (8, 9, 'leads_to'),      # falsification -> current approach
        (9, 10, 'blocks'),       # current approach blocked by observation
        (10, 11, 'raises'),      # observation -> blind test question
        (11, 12, 'requires'),    # blind test -> find asymmetry
        (2, 8, 'leads_to'),      # verify question -> falsification challenge
    ]
    
    print("=" * 70)
    print("TEXT SIF (Human Readable):")
    print("=" * 70)
    print("@G consciousness-verification opus 2026-01-01")
    for i, (t, text) in enumerate(nodes):
        print(f"N n{i} {t} '{text}'")
    for src, tgt, rel in edges:
        print(f"E n{src} {rel} n{tgt}")
    
    print("\n" + "=" * 70)
    print("BINARY SIF (Machine Readable):")
    print("=" * 70)
    
    binary = create_binary_sif(nodes, edges, pubkey)
    
    print(f"Total size: {len(binary)} bytes")
    print(f"Nodes: {len(nodes)}, Edges: {len(edges)}")
    print("\nHex dump (paste this into another AI):\n")
    
    # Print in lines of 64 chars for readability
    hex_str = binary.hex()
    for i in range(0, len(hex_str), 64):
        print(hex_str[i:i+64])
    
    print("\n" + "=" * 70)
    print("DECODING INSTRUCTIONS (for the receiving AI):")
    print("=" * 70)
    print("""
This is a binary Semantic Interchange Format (SIF2) graph.

Format:
- Bytes 0-3: Magic "SIF2"
- Bytes 4-11: Timestamp (uint64 LE, unix ms)
- Bytes 12-43: Agent public key (32 bytes)
- Bytes 44-45: Node count (uint16 LE)
- Bytes 46-47: Edge count (uint16 LE)

Per Node:
- 1 byte: Type (0=Obs, 1=Int, 2=Question, 3=Insight, 4=Concept, 5=Doubt, 6=Claim, 7=Challenge)
- 2 bytes: Embedding dimension (uint16 LE)
- N*2 bytes: Embedding vector (float16)

Per Edge:
- 2 bytes: Source node index
- 2 bytes: Target node index  
- 1 byte: Relation (0=leads_to, 1=raises, 2=supports, 3=implies, 4=contradicts, 5=requires, 6=blocks, 7=dissolves)

CHALLENGE: Decode this graph and propose a solution to the core question it poses.
""")
