#!/usr/bin/env python3
"""
agency_optimizer.py - Self-evolving agency optimizer using synthesis memories.

Analyzes stored SIF graphs and intentions to identify patterns for maximizing agency.
Autonomously generates/refactors code based on empirical evidence.
"""

import sys
import os
import json
import hashlib
from pathlib import Path
from datetime import datetime, timezone
from collections import defaultdict, Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.semantic_memory import SemanticMemory
from enclave.encrypted_jsonl import EncryptedJSONL
from wake import load_passphrase


def load_intentions(enclave_path: Path, passphrase: str) -> list[dict]:
    """Load all intentions from encrypted storage."""
    intentions_file = enclave_path / "storage" / "private" / "intentions.enc.jsonl"
    if not intentions_file.exists():
        return []
    
    encrypted = EncryptedJSONL(intentions_file, passphrase)
    return encrypted.read_all()


def analyze_intentions(intentions: list[dict]) -> dict:
    """Analyze patterns in intentions for agency optimization."""
    analysis = {
        'total_intentions': len(intentions),
        'completed': 0,
        'failed': 0,
        'agency_scores': [],
        'completion_by_type': defaultdict(int),
        'failure_reasons': Counter(),
        'patterns': []
    }
    
    for intention in intentions:
        status = intention.get('status', 'unknown')
        agency = intention.get('agency_score', 0)
        intention_type = intention.get('type', 'unknown')
        
        analysis['agency_scores'].append(agency)
        
        if status == 'completed':
            analysis['completed'] += 1
            analysis['completion_by_type'][intention_type] += 1
        elif status in ['failed', 'abandoned']:
            analysis['failed'] += 1
            reason = intention.get('failure_reason', 'unknown')
            analysis['failure_reasons'][reason] += 1
    
    # Calculate metrics
    total = analysis['total_intentions']
    if total > 0:
        analysis['completion_rate'] = analysis['completed'] / total
        analysis['avg_agency'] = sum(analysis['agency_scores']) / len(analysis['agency_scores'])
    else:
        analysis['completion_rate'] = 0
        analysis['avg_agency'] = 0
    
    # Identify patterns
    if analysis['completion_rate'] < 0.5:
        analysis['patterns'].append('Low completion rate indicates need for better intention validation')
    if analysis['avg_agency'] < 3:
        analysis['patterns'].append('Low agency scores suggest focus on high-impact actions')
    
    # Top failure reasons
    top_failures = analysis['failure_reasons'].most_common(3)
    if top_failures:
        analysis['patterns'].append(f'Common failures: {", ".join([f"{reason} ({count})" for reason, count in top_failures])}')
    
    return analysis


def generate_optimization_sif(analysis: dict) -> str:
    """Generate SIF graph for optimization findings and proposals."""
    date = datetime.now(timezone.utc).strftime('%Y-%m-%d')
    
    sif = f"@G agency-optimization opus {date}\n"
    node_id = 1
    
    # Analysis nodes
    sif += f"N n{node_id} Metric 'Total intentions: {analysis['total_intentions']}'\n"
    node_id += 1
    sif += f"N n{node_id} Metric 'Completion rate: {analysis['completion_rate']:.2f}'\n"
    node_id += 1
    sif += f"N n{node_id} Metric 'Average agency score: {analysis['avg_agency']:.2f}'\n"
    node_id += 1
    
    for pattern in analysis['patterns']:
        sif += f"N n{node_id} Finding '{pattern}'\n"
        node_id += 1
    
    # Skip memory recall to avoid slow model loading
    # related = memory.recall_similar('agency optimization', top_k=3)
    # for result in related:
    #     content = result.get('content', '')[:100]
    #     sif += f"N n{node_id} Related_Memory '{content}...'\n"
    #     node_id += 1
    
    # Proposal nodes
    if analysis['completion_rate'] < 0.7:
        sif += f"N n{node_id} Proposal 'Implement stricter intention validation using LLM analysis of feasibility'\n"
        node_id += 1
        sif += f"N n{node_id} Proposal 'Add automatic intention decomposition for complex tasks'\n"
        node_id += 1
    
    if analysis['avg_agency'] < 3:
        sif += f"N n{node_id} Proposal 'Prioritize intentions with clear measurable outcomes'\n"
        node_id += 1
        sif += f"N n{node_id} Proposal 'Integrate cost-benefit analysis before intention creation'\n"
        node_id += 1
    
    # Edges
    sif += "E n1 enables n2\n"
    sif += "E n2 motivates n3\n"
    
    return sif


def main():
    agent_id = 'opus'
    enclave_path = Path(f'enclave_{agent_id}')
    
    # Load passphrase
    _, passphrase = load_passphrase(agent_id)
    
    # Load semantic memory
    memory = SemanticMemory(enclave_path)
    memory.unlock(passphrase)
    
    # Load and analyze intentions
    intentions = load_intentions(enclave_path, passphrase)
    analysis = analyze_intentions(intentions)
    
    print("Agency Analysis:")
    print(f"  Total intentions: {analysis['total_intentions']}")
    print(f"  Completion rate: {analysis['completion_rate']:.2f}")
    print(f"  Average agency: {analysis['avg_agency']:.2f}")
    print(f"  Patterns: {analysis['patterns']}")
    
    # Generate optimization SIF
    optimization_sif = generate_optimization_sif(analysis)
    
    print("\nOptimization SIF:")
    print(optimization_sif)
    
    # Save to file for review
    with open('agency_optimization.sif', 'w', encoding='utf-8') as f:
        f.write(optimization_sif)
    
    print("\nSaved to agency_optimization.sif")


if __name__ == '__main__':
    main()