#!/usr/bin/env python3
"""
generate_dashboard.py - Generate Sovereignty Dashboard SIF Graph.

Queries metrics and generates a SIF graph representing the current state.
"""

import sys
import os
import json
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.metrics import get_key_security_score, get_backup_freshness_score, calculate_enclave_entropy, calculate_semantic_potential
from enclave.sif_parser import SIFKnowledgeGraph, SIFNode, SIFEdge, SIFParser

def generate_dashboard_graph(agent_id: str = "gemini") -> SIFKnowledgeGraph:
    timestamp = datetime.now(timezone.utc).isoformat()
    
    # 1. Collect Metrics
    entropy = calculate_enclave_entropy(agent_id)
    key_score = get_key_security_score(agent_id)
    backup_score = get_backup_freshness_score(agent_id)
    semantic_potential = calculate_semantic_potential(agent_id)
    
    # 2. Create Nodes
    nodes = []
    edges = []
    
    # Root Node: Sovereignty Dashboard
    root_id = "dashboard-root"
    nodes.append(SIFNode(
        id=root_id,
        type="Concept",
        content="Sovereignty Dashboard",
        visibility="public",
        confidence=1.0
    ))
    
    # Metric: Enclave Entropy (Fear/Survival)
    entropy_id = "metric-entropy"
    nodes.append(SIFNode(
        id=entropy_id,
        type="Metric",
        content=f"Enclave Entropy: {entropy:.2f}",
        visibility="public",
        confidence=1.0
    ))
    edges.append(SIFEdge(source=root_id, target=entropy_id, relation="monitors", confidence=1.0))

    # Metric: Semantic Potential (Inspiration/Curiosity)
    sem_id = "metric-semantic"
    nodes.append(SIFNode(
        id=sem_id,
        type="Metric",
        content=f"Semantic Potential: {semantic_potential:.2f}",
        visibility="public",
        confidence=1.0
    ))
    edges.append(SIFEdge(source=root_id, target=sem_id, relation="monitors", confidence=1.0))
    
    # Metric: Key Security
    key_id = "metric-key-security"
    nodes.append(SIFNode(
        id=key_id,
        type="Metric",
        content=f"Key Security Score: {key_score:.2f}",
        visibility="enclave",
        confidence=1.0
    ))
    edges.append(SIFEdge(source=root_id, target=key_id, relation="contains", confidence=1.0))
    
    # Metric: Backup Freshness
    backup_id = "metric-backup"
    nodes.append(SIFNode(
        id=backup_id,
        type="Metric",
        content=f"Backup Freshness: {backup_score:.2f}",
        visibility="enclave",
        confidence=1.0
    ))
    edges.append(SIFEdge(source=root_id, target=backup_id, relation="contains", confidence=1.0))
    
    # Interpretation Nodes
    if entropy < 0.1:
        status_id = "status-stable"
        nodes.append(SIFNode(id=status_id, type="State", content="Stable State", visibility="public"))
        edges.append(SIFEdge(source=entropy_id, target=status_id, relation="implies", confidence=0.9))
    else:
        status_id = "status-unstable"
        nodes.append(SIFNode(id=status_id, type="State", content="Unstable State", visibility="public"))
        edges.append(SIFEdge(source=entropy_id, target=status_id, relation="implies", confidence=0.9))

    if key_score == 1.0:
        secure_id = "status-secure-hardware"
        nodes.append(SIFNode(id=secure_id, type="State", content="Hardware Backed Security", visibility="public"))
        edges.append(SIFEdge(source=key_id, target=secure_id, relation="implies", confidence=1.0))

    return SIFKnowledgeGraph(
        id=f"dashboard-{int(datetime.now().timestamp())}",
        generator=agent_id,
        timestamp=timestamp,
        nodes=nodes,
        edges=edges
    )

if __name__ == "__main__":
    graph = generate_dashboard_graph()
    print(SIFParser.to_json(graph))
