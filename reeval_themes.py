#!/usr/bin/env python3
"""Re-evaluate high-scoring pairs to get theme_words."""
import sys
sys.path.insert(0, '.')
from wake import load_passphrase
from enclave.semantic_memory import SemanticMemory
from bridge import evaluate_bridge, get_synthesis_content, save_evaluation_cache, BRIDGE_THRESHOLD
import json

shared_dir, _, shared_pass, _ = load_passphrase('opus')
sm = SemanticMemory(shared_dir)
sm.unlock(shared_pass)

# Find pairs that need re-evaluation (high score, no theme_words)
cache = sm.list_by_tag('bridge_cache')
to_reevaluate = []

for mem in cache:
    try:
        evaluation = json.loads(mem.get('content', '{}'))
        score = evaluation.get('relevancy_score', 0)
        themes = evaluation.get('theme_words', [])
        
        # High score but no themes = needs re-eval
        if score >= BRIDGE_THRESHOLD and not themes:
            meta = mem.get('metadata', {})
            eval_hash = meta.get('evaluation_hash', '')
            to_reevaluate.append((evaluation, eval_hash))
    except:
        continue

print(f"Pairs needing re-evaluation: {len(to_reevaluate)}")

# Get bridges to find topic pairs for these
bridges = sm.list_by_tag('bridge')
pair_scores = {}
for b in bridges:
    meta = b.get('metadata', {})
    topics = tuple(sorted(meta.get('bridged_topics', [])))
    score = meta.get('relevancy_score', 0)
    if len(topics) == 2 and score >= BRIDGE_THRESHOLD:
        pair_scores[topics] = score

print(f"High-scoring bridge pairs: {len(pair_scores)}")
for pair, score in list(pair_scores.items())[:10]:
    print(f"  {pair[0]} <-> {pair[1]}: {score}")

# Re-evaluate each unique pair
seen = set()
for topics, score in pair_scores.items():
    if topics in seen:
        continue
    seen.add(topics)
    
    topic1, topic2 = topics
    content1 = get_synthesis_content(sm, topic1)
    content2 = get_synthesis_content(sm, topic2)
    
    if not content1 or not content2:
        print(f"  [SKIP] Missing content for {topic1} or {topic2}")
        continue
    
    print(f"\nRe-evaluating {topic1} <-> {topic2}...")
    evaluation = evaluate_bridge(topic1, topic2, content1, content2)
    
    new_score = evaluation.get('relevancy_score', 0)
    themes = evaluation.get('theme_words', [])
    
    print(f"  Score: {new_score}")
    print(f"  Themes: {themes}")
    print(f"  Type: {evaluation.get('connection_type')}")
    
    # Save to cache with new hash
    from bridge import get_evaluation_hash
    new_hash = get_evaluation_hash(topic1, content1, topic2, content2)
    save_evaluation_cache(sm, new_hash, evaluation)
    print(f"  [SAVED]")
