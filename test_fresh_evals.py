#!/usr/bin/env python3
"""Test fresh bridge evaluations to get theme_words."""
import sys
sys.path.insert(0, '.')

# Force fresh imports
import importlib
import bridge
importlib.reload(bridge)

from wake import load_passphrase
from enclave.semantic_memory import SemanticMemory
from bridge import (evaluate_bridge, get_synthesis_content, 
                    save_evaluation_cache, get_evaluation_hash, BRIDGE_THRESHOLD)
import json

shared_dir, _, shared_pass, _ = load_passphrase('opus')
sm = SemanticMemory(shared_dir)
sm.unlock(shared_pass)

print("Testing get_synthesis_content directly...")
test_result = get_synthesis_content(sm, 'agency-autonomy')
print(f"  agency-autonomy found: {test_result is not None}")

# Test pairs that we know had high scores
test_pairs = [
    ('agency-autonomy', 'semantic-memory'),  # Was 0.92
    ('blind-spots', 'dream'),                # Was 0.92  
    ('agency-autonomy', 'entropy'),          # Was 0.80
    ('cryptography', 'risk'),                # Was 0.70
]

for topic1, topic2 in test_pairs:
    content1 = get_synthesis_content(sm, topic1)
    content2 = get_synthesis_content(sm, topic2)
    
    if not content1:
        print(f"[SKIP] No synthesis for {topic1}")
        continue
    if not content2:
        print(f"[SKIP] No synthesis for {topic2}")
        continue
    
    print(f"\n{'='*60}")
    print(f"Evaluating: {topic1} <-> {topic2}")
    print(f"{'='*60}")
    
    evaluation = evaluate_bridge(topic1, topic2, content1, content2)
    
    score = evaluation.get('relevancy_score', 0)
    themes = evaluation.get('theme_words', [])
    conn_type = evaluation.get('connection_type', '?')
    explanation = evaluation.get('explanation', '')[:200]
    insight = evaluation.get('bridge_insight', '')[:200]
    
    print(f"Score: {score}")
    print(f"Type: {conn_type}")
    print(f"Theme words: {themes}")
    print(f"Explanation: {explanation}")
    print(f"Insight: {insight}")
    
    # Save to cache
    if score >= BRIDGE_THRESHOLD and themes:
        eval_hash = get_evaluation_hash(topic1, content1, topic2, content2)
        save_evaluation_cache(sm, eval_hash, evaluation)
        print(f"[CACHED with themes]")
