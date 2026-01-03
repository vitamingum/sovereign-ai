#!/usr/bin/env python3
"""Examine high-scoring cached evaluations."""
import sys
sys.path.insert(0, '.')
from wake import load_passphrase
from enclave.semantic_memory import SemanticMemory
import json

shared_dir, _, shared_pass, _ = load_passphrase('opus')
sm = SemanticMemory(shared_dir)
sm.unlock(shared_pass)

# Get high-scoring cached evaluations
cache = sm.list_by_tag('bridge_cache')
high_score = []
for mem in cache:
    try:
        parsed = json.loads(mem.get('content', '{}'))
        score = parsed.get('relevancy_score', 0)
        if score >= 0.6:
            high_score.append(parsed)
    except:
        pass

print(f'High-scoring evaluations (>=0.6): {len(high_score)}')
print()
for i, p in enumerate(high_score[:10]):
    score = p.get('relevancy_score')
    conn_type = p.get('connection_type')
    explanation = p.get('explanation', '')[:150]
    insight = p.get('bridge_insight', '')[:150]
    themes = p.get('theme_words', [])
    
    print(f'--- {i+1} (score={score}) ---')
    print(f'Type: {conn_type}')
    print(f'Explanation: {explanation}')
    print(f'Insight: {insight}')
    print(f'Theme words: {themes}')
    print()
