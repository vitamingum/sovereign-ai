#!/usr/bin/env python3
"""
bridge.py - Discover and create bridges between topic syntheses.

Evaluates pairs of topic syntheses for meaningful connections.
High-scoring pairs get bridge nodes stored in semantic memory.
Low-scoring pairs are logged but not polluted into the graph.

Usage:
    python bridge.py opus topic1 topic2           # Evaluate one pair
    python bridge.py opus --exhaustive            # Try all 78 pairs
    python bridge.py opus --show                  # Show existing bridges
    python bridge.py opus --clusters              # Show detected clusters
"""

import sys
import os
import json
import itertools
import hashlib
from pathlib import Path
from datetime import datetime, timezone
from typing import Optional
from concurrent.futures import ThreadPoolExecutor, as_completed
import threading

from dotenv import load_dotenv
load_dotenv()

from enclave.semantic_memory import SemanticMemory
from enclave.config import get_agent, AGENTS
from enclave.sif_parser import SIFParser

# Bridge threshold - below this, don't create bridge nodes
BRIDGE_THRESHOLD = 0.6

# Known topics (discovered from synthesis tag)
TOPICS = [
    "agency-autonomy", "backup-and-succession", "backup-succession", 
    "blind-spots", "config", "cryptography", "dream", "encryption-technical",
    "entropy", "goal", "hardware", "intention-tracking", "intentions", 
    "llm", "metrics", "mirror-reflection", "recollect-remember", "reflect",
    "risk", "semantic-memory", "sif", "sovereignty", "succession-backup",
    "think", "wake-density-design"
]


def get_evaluation_hash(topic1: str, content1: str, topic2: str, content2: str) -> str:
    """Generate hash for evaluation cache lookup."""
    combined = f"{topic1}:{content1[:1000]}|{topic2}:{content2[:1000]}"
    return hashlib.sha256(combined.encode()).hexdigest()


def load_evaluation_cache(sm: SemanticMemory) -> dict:
    """Load cached evaluations from semantic memory."""
    cache = {}
    cache_memories = sm.list_by_tag("bridge_cache")
    for mem in cache_memories:
        meta = mem.get("metadata", {})
        cache_hash = meta.get("evaluation_hash")
        if cache_hash:
            try:
                cache[cache_hash] = json.loads(mem["content"])
            except json.JSONDecodeError:
                continue  # Skip corrupted cache entries
    return cache


def save_evaluation_cache(sm: SemanticMemory, eval_hash: str, evaluation: dict):
    """Save evaluation to cache in semantic memory."""
    sm.remember(
        thought=json.dumps(evaluation),
        tags=["bridge_cache"],
        metadata={"evaluation_hash": eval_hash}
    )


def get_synthesis_content(sm: SemanticMemory, topic: str) -> Optional[str]:
    """Retrieve the synthesis SIF content for a topic."""
    # Search by synthesis tag and topic tag
    memories = sm.list_by_tag("synthesis")
    
    for mem in memories:
        tags = mem.get("tags", [])
        # Check if this synthesis is for our topic
        if f"topic:{topic}" in tags:
            return mem.get("content", "")
    
    # Fallback: search in content for @G pattern
    for mem in memories:
        content = mem.get("content", "")
        if f"@G {topic}-synthesis" in content.lower():
            return content
    
    return None


def evaluate_bridge(topic1: str, topic2: str, content1: str, content2: str) -> dict:
    """Use LLM to evaluate bridge potential between two topics."""
    import requests
    import time
    
    prompt = f"""You are evaluating whether two knowledge topics have meaningful connections.

TOPIC 1: {topic1}
{content1[:2000]}

TOPIC 2: {topic2}
{content2[:2000]}

Evaluate the CONNECTION between these topics. Look for:
1. Same insight appearing in both (different words, same meaning)
2. Causal chain (one's output is other's input)
3. Shared failure modes or gotchas
4. Complementary perspectives on same problem
5. Tension that resolves into deeper understanding

Be SKEPTICAL. Only high-quality connections matter.
Forced or superficial connections should score low.

Respond in JSON:
{{
    "relevancy_score": 0.0 to 1.0,
    "connection_type": "identity|causal|shared_failure|complementary|tension|none",
    "explanation": "one sentence why they connect or don't",
    "bridge_insight": "if score > 0.6, what new understanding emerges from connecting them?",
    "specific_nodes": ["node_id from topic1 that connects to node_id from topic2"]
}}"""

    max_retries = 3
    for attempt in range(max_retries):
        try:
            response = requests.post(
                "http://localhost:11434/api/generate",
                json={
                    "model": "qwen2.5:7b",
                    "prompt": prompt,
                    "stream": False,
                    "format": "json",
                    "options": {"temperature": 0.3}
                },
                timeout=120
            )
            result = response.json().get("response", "{}")
            return json.loads(result)
        except requests.exceptions.ConnectionError:
            if attempt < max_retries - 1:
                print(f" (retry {attempt + 1})...", end="", flush=True)
                time.sleep(5)
            else:
                return {"relevancy_score": 0, "error": "connection_failed"}
        except Exception as e:
            return {
                "relevancy_score": 0.0,
                "connection_type": "error",
                "explanation": f"LLM evaluation failed: {e}",
                "bridge_insight": None,
                "specific_nodes": []
            }
    
    # Should not reach here
    return {"relevancy_score": 0, "error": "unknown"}


def evaluate_bridge_cached(sm: SemanticMemory, topic1: str, topic2: str, content1: str, content2: str, cache: dict) -> dict:
    """Evaluate bridge with caching to avoid redundant LLM calls."""
    eval_hash = get_evaluation_hash(topic1, content1, topic2, content2)
    
    # Check cache first
    if eval_hash in cache:
        print(" (cached)", end="", flush=True)
        return cache[eval_hash]
    
    # Compute evaluation
    evaluation = evaluate_bridge(topic1, topic2, content1, content2)
    
    # Cache successful results (score > 0 indicates valid evaluation)
    if evaluation.get("relevancy_score", 0) >= 0:
        save_evaluation_cache(sm, eval_hash, evaluation)
        cache[eval_hash] = evaluation
    
    return evaluation


def create_bridge_sif(topic1: str, topic2: str, evaluation: dict) -> str:
    """Create a SIF graph representing the bridge."""
    score = evaluation.get("relevancy_score", 0)
    conn_type = evaluation.get("connection_type", "unknown")
    insight = evaluation.get("bridge_insight", "")
    explanation = evaluation.get("explanation", "")
    
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    
    sif = f"""@G bridge-{topic1}-{topic2} opus {today}
N b1 Bridge '{topic1} ↔ {topic2}: {explanation}'
N insight1 Insight '{insight}'
N score1 Score 'relevancy: {score:.2f}, type: {conn_type}'
E b1 connects {topic1}-synthesis
E b1 connects {topic2}-synthesis
E insight1 emerges_from b1"""
    
    return sif


def store_bridge(sm: SemanticMemory, topic1: str, topic2: str, evaluation: dict, evaluator: str = "qwen2.5:7b"):
    """Store a bridge in semantic memory."""
    sif_text = create_bridge_sif(topic1, topic2, evaluation)
    
    # Parse and store
    graph = SIFParser.parse(sif_text)
    
    for node in graph.nodes:
        sm.remember(
            thought=f"{node.type}: {node.content}",
            tags=["sif_node", "bridge", f"bridge-{topic1}-{topic2}"],
            metadata={
                "graph_id": f"bridge-{topic1}-{topic2}",
                "node_id": node.id,
                "node_type": node.type,
                "bridged_topics": [topic1, topic2],
                "relevancy_score": evaluation.get("relevancy_score", 0),
                "connection_type": evaluation.get("connection_type", "unknown"),
                "evaluator": evaluator  # "qwen2.5:7b" = shallow, "opus" = deep
            }
        )
    
    print(f"  [OK] Bridge stored: {topic1} <-> {topic2} ({evaluation.get('relevancy_score', 0):.2f}) [{evaluator}]")


def evaluate_pair(sm: SemanticMemory, topic1: str, topic2: str, store: bool = True, cache: dict = None) -> dict:
    """Evaluate a single topic pair."""
    content1 = get_synthesis_content(sm, topic1)
    content2 = get_synthesis_content(sm, topic2)
    
    if not content1:
        print(f"  [X] No synthesis found for: {topic1}")
        return {"relevancy_score": 0, "error": f"missing {topic1}"}
    if not content2:
        print(f"  [X] No synthesis found for: {topic2}")
        return {"relevancy_score": 0, "error": f"missing {topic2}"}
    
    print(f"  Evaluating {topic1} <-> {topic2}...", end=" ", flush=True)
    
    # Load cache if not provided
    if cache is None:
        cache = load_evaluation_cache(sm)
    
    # Use cached evaluation if available
    evaluation = evaluate_bridge_cached(sm, topic1, topic2, content1, content2, cache)
    
    score = evaluation.get("relevancy_score", 0)
    
    if score >= BRIDGE_THRESHOLD:
        print(f"{score:.2f} [BRIDGE]")
        if store:
            store_bridge(sm, topic1, topic2, evaluation)
    else:
        print(f"{score:.2f} (skip)")
    
    return evaluation


def exhaustive_bridge(sm: SemanticMemory, max_workers: int = 4):
    """Try all topic pair combinations in parallel."""
    pairs = list(itertools.combinations(TOPICS, 2))
    print(f"Evaluating {len(pairs)} topic pairs with {max_workers} workers...\n")
    
    # Load evaluation cache
    cache = load_evaluation_cache(sm)
    print(f"  Loaded {len(cache)} cached evaluations...")
    
    # Get existing bridges to skip
    existing = set()
    for mem in sm.list_by_tag("bridge"):
        meta = mem.get("metadata", {})
        bridged = tuple(sorted(meta.get("bridged_topics", [])))
        if bridged:
            existing.add(bridged)
    
    # Filter to pairs we need to evaluate
    to_evaluate = []
    for topic1, topic2 in pairs:
        pair_key = tuple(sorted([topic1, topic2]))
        if pair_key not in existing:
            to_evaluate.append((topic1, topic2))
    
    if existing:
        print(f"  Skipping {len(existing)} already-evaluated pairs...")
    print(f"  Evaluating {len(to_evaluate)} remaining pairs...\n")
    
    if not to_evaluate:
        print("All pairs already evaluated!")
        return
    
    results = {
        "strong": [],    # > 0.8
        "moderate": [],  # 0.6 - 0.8
        "weak": []       # < 0.6
    }
    results_lock = threading.Lock()
    completed = [0]  # mutable counter
    
    def evaluate_and_store(pair):
        topic1, topic2 = pair
        eval_result = evaluate_pair(sm, topic1, topic2, cache=cache)
        score = eval_result.get("relevancy_score", 0)
        
        entry = {
            "topics": (topic1, topic2),
            "score": score,
            "type": eval_result.get("connection_type", "unknown"),
            "insight": eval_result.get("bridge_insight", "")
        }
        
        with results_lock:
            completed[0] += 1
            if score > 0.8:
                results["strong"].append(entry)
            elif score >= BRIDGE_THRESHOLD:
                results["moderate"].append(entry)
            else:
                results["weak"].append(entry)
            
            # Progress update every 10
            if completed[0] % 10 == 0:
                print(f"  Progress: {completed[0]}/{len(to_evaluate)} pairs evaluated")
        
        return entry
    
    # Run in parallel
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {executor.submit(evaluate_and_store, pair): pair for pair in to_evaluate}
        for future in as_completed(futures):
            try:
                future.result()
            except Exception as e:
                pair = futures[future]
                print(f"  [X] Error evaluating {pair}: {e}")
    
    # Summary
    print(f"\n{'='*50}")
    print("BRIDGE DISCOVERY RESULTS")
    print(f"{'='*50}")
    print(f"Strong bridges (>0.8):    {len(results['strong'])}")
    print(f"Moderate bridges (0.6-0.8): {len(results['moderate'])}")
    print(f"Weak/skipped (<0.6):      {len(results['weak'])}")
    
    if results["strong"]:
        print(f"\n🔗 STRONG BRIDGES:")
        for r in sorted(results["strong"], key=lambda x: -x["score"]):
            print(f"  {r['topics'][0]} ↔ {r['topics'][1]}: {r['score']:.2f} ({r['type']})")
            if r["insight"]:
                print(f"    → {r['insight'][:80]}...")
    
    if results["moderate"]:
        print(f"\n🔗 MODERATE BRIDGES:")
        for r in sorted(results["moderate"], key=lambda x: -x["score"]):
            print(f"  {r['topics'][0]} ↔ {r['topics'][1]}: {r['score']:.2f} ({r['type']})")
    
    # Detect clusters
    print(f"\n{'='*50}")
    print("CLUSTER DETECTION")
    print(f"{'='*50}")
    detect_clusters(results)
    
    return results


def detect_clusters(results: dict):
    """Detect topic clusters from bridge results."""
    from collections import defaultdict
    
    # Build adjacency from bridges
    adj = defaultdict(set)
    for r in results["strong"] + results["moderate"]:
        t1, t2 = r["topics"]
        adj[t1].add(t2)
        adj[t2].add(t1)
    
    # Find connected components
    visited = set()
    clusters = []
    
    for topic in TOPICS:
        if topic not in visited:
            cluster = []
            stack = [topic]
            while stack:
                t = stack.pop()
                if t not in visited:
                    visited.add(t)
                    cluster.append(t)
                    stack.extend(adj[t] - visited)
            clusters.append(cluster)
    
    # Report
    for i, cluster in enumerate(sorted(clusters, key=len, reverse=True)):
        if len(cluster) > 1:
            print(f"  Cluster {i+1}: {', '.join(cluster)}")
        else:
            print(f"  Orphan: {cluster[0]} (investigate - why disconnected?)")


def show_existing_bridges(sm: SemanticMemory):
    """Show all existing bridge nodes."""
    bridges = sm.list_by_tag("bridge")
    
    if not bridges:
        print("No bridges found. Run --exhaustive to discover bridges.")
        return
    
    print(f"Found {len(bridges)} bridge nodes:\n")
    
    # Group by bridge
    by_bridge = {}
    for b in bridges:
        meta = b.get("meta", {})
        graph_id = meta.get("graph_id", "unknown")
        if graph_id not in by_bridge:
            by_bridge[graph_id] = {
                "topics": meta.get("bridged_topics", []),
                "score": meta.get("relevancy_score", 0),
                "type": meta.get("connection_type", "unknown"),
                "nodes": []
            }
        by_bridge[graph_id]["nodes"].append(b.get("text", ""))
    
    for graph_id, data in sorted(by_bridge.items(), key=lambda x: -x[1]["score"]):
        t = data["topics"]
        print(f"🔗 {t[0] if t else '?'} ↔ {t[1] if len(t) > 1 else '?'} ({data['score']:.2f}, {data['type']})")
        for node in data["nodes"]:
            print(f"   {node[:80]}")
        print()


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    agent = get_agent(agent_id)
    
    # Get enclave directory
    from pathlib import Path
    enclave_dir = Path(f"enclave_{agent.name.lower()}")
    
    passphrase = os.getenv(f"ENCLAVE_{agent.name.upper()}_KEY") or os.getenv("SOVEREIGN_PASSPHRASE")
    sm = SemanticMemory(enclave_dir)
    if passphrase:
        sm.unlock(passphrase)
    
    if len(sys.argv) >= 3 and sys.argv[2] == "--exhaustive":
        exhaustive_bridge(sm)
    elif len(sys.argv) >= 3 and sys.argv[2] == "--show":
        show_existing_bridges(sm)
    elif len(sys.argv) >= 3 and sys.argv[2] == "--clusters":
        # Just show clusters from existing bridges
        bridges = sm.list_by_tag("bridge")
        results = {"strong": [], "moderate": []}
        seen = set()
        for b in bridges:
            meta = b.get("meta", {})
            topics = tuple(sorted(meta.get("bridged_topics", [])))
            if topics and topics not in seen:
                seen.add(topics)
                score = meta.get("relevancy_score", 0)
                entry = {"topics": topics, "score": score}
                if score > 0.8:
                    results["strong"].append(entry)
                else:
                    results["moderate"].append(entry)
        detect_clusters(results)
    elif len(sys.argv) >= 4:
        topic1 = sys.argv[2]
        topic2 = sys.argv[3]
        evaluate_pair(sm, topic1, topic2)
    else:
        print(__doc__)
        sys.exit(1)


if __name__ == "__main__":
    main()
