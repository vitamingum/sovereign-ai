#!/usr/bin/env python3
"""Check anchor structure."""
import sys
sys.path.insert(0, '.')
from wake import load_passphrase
from enclave.semantic_memory import SemanticMemory
import json

shared_dir, _, shared_pass, _ = load_passphrase('opus')
sm = SemanticMemory(shared_dir)
sm.unlock(shared_pass)

# Test get_file_understandings logic manually
anchors = sm.list_by_tag("anchor")
print(f"Total anchors: {len(anchors)}")

for anchor in anchors[:3]:
    meta = anchor.get("metadata", {})
    target = meta.get("target_path", "")
    graph_id = meta.get("graph_id", "")
    
    print(f"\n--- Anchor ---")
    print(f"target_path: {target}")
    print(f"graph_id: {graph_id}")
    
    if not target or not graph_id:
        print("SKIP: missing target or graph_id")
        continue
    
    # Get nodes with this tag
    nodes = sm.list_by_tag(graph_id)
    print(f"Nodes with tag '{graph_id}': {len(nodes)}")
    
    # Collect content
    file_content = []
    for node in nodes:
        node_tags = node.get("tags", [])
        if "anchor" in node_tags:
            continue
        content = node.get("content", "")
        if content:
            file_content.append(content[:50])
    
    print(f"Content pieces: {len(file_content)}")
    if file_content:
        print(f"Sample: {file_content[0]}")
