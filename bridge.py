#!/usr/bin/env python3
"""
bridge.py - Discover themes connecting topic syntheses.

Evaluates pairs of topic syntheses for meaningful connections,
extracting theme words that reveal underlying patterns.
Themes aggregate across pairs to show what syntheses to write.

Usage:
    python bridge.py opus                         # Show theme clusters (default)
    python bridge.py opus --refresh               # Re-evaluate all pairs, then show themes
    python bridge.py opus --raw                   # Show raw bridges without theme aggregation
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


def get_actual_synthesis_topics(sm: SemanticMemory) -> list[str]:
    """Dynamically discover actual synthesis topics from semantic memory."""
    syntheses = sm.list_by_tag("synthesis")
    topics = set()
    
    for s in syntheses:
        tags = s.get("tags", [])
        for tag in tags:
            if tag.startswith("topic:"):
                topics.add(tag[6:])  # Remove 'topic:' prefix
    
    return sorted(list(topics))


def get_evaluation_hash(topic1: str, content1: str, topic2: str, content2: str) -> str:
    """Generate hash for evaluation cache lookup."""
    combined = f"{topic1}:{content1[:1000]}|{topic2}:{content2[:1000]}"
    return hashlib.sha256(combined.encode()).hexdigest()


def load_evaluation_cache(sm: SemanticMemory, require_themes: bool = True) -> dict:
    """Load cached evaluations from semantic memory.
    
    Args:
        sm: SemanticMemory instance
        require_themes: If True, skip cache entries without theme_words (forces re-eval)
    """
    cache = {}
    cache_memories = sm.list_by_tag("bridge_cache")
    for mem in cache_memories:
        meta = mem.get("metadata", {})
        cache_hash = meta.get("evaluation_hash")
        if cache_hash:
            try:
                evaluation = json.loads(mem["content"])
                # Skip entries without theme_words if required (old format)
                if require_themes and not evaluation.get("theme_words"):
                    continue
                cache[cache_hash] = evaluation
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
    "theme_words": ["2-4 abstract nouns that capture WHY these connect, e.g. resilience, continuity, identity"],
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
    theme_words = evaluation.get("theme_words", [])
    
    if score >= BRIDGE_THRESHOLD:
        themes_str = f" → {', '.join(theme_words)}" if theme_words else ""
        print(f"{score:.2f} [BRIDGE]{themes_str}")
        if store:
            store_bridge(sm, topic1, topic2, evaluation)
    else:
        print(f"{score:.2f} (skip)")
    
    return evaluation


def exhaustive_bridge(sm: SemanticMemory, max_workers: int = 4):
    """Try all topic pair combinations in parallel."""
    # Use actual synthesis topics instead of hardcoded list
    actual_topics = get_actual_synthesis_topics(sm)
    pairs = list(itertools.combinations(actual_topics, 2))
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
    detect_clusters(results, sm)
    
    return results


def detect_clusters(results: dict, sm: SemanticMemory = None):
    """Detect topic clusters from bridge results."""
    from collections import defaultdict
    
    # Use actual topics if semantic memory provided
    if sm:
        topic_list = get_actual_synthesis_topics(sm)
    else:
        topic_list = TOPICS
    
    # Build adjacency from bridges
    adj = defaultdict(set)
    for r in results["strong"] + results["moderate"]:
        t1, t2 = r["topics"]
        adj[t1].add(t2)
        adj[t2].add(t1)
    
    # Find connected components
    visited = set()
    clusters = []
    
    for topic in topic_list:
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


def aggregate_themes(sm: SemanticMemory) -> dict:
    """Aggregate theme words from cached evaluations into theme clusters.
    
    Returns:
        {
            "themes": {
                "resilience": {"topics": {"backup", "risk", "crypto"}, "pairs": [...], "score_sum": 2.4},
                ...
            },
            "total_evaluations": 25,
            "pairs_with_themes": 18
        }
    """
    from collections import defaultdict
    
    cache_memories = sm.list_by_tag("bridge_cache")
    
    themes = defaultdict(lambda: {"topics": set(), "pairs": [], "score_sum": 0.0})
    total = 0
    with_themes = 0
    
    for mem in cache_memories:
        try:
            evaluation = json.loads(mem.get("content", "{}"))
            total += 1
            
            score = evaluation.get("relevancy_score", 0)
            if score < BRIDGE_THRESHOLD:
                continue  # Skip weak connections
            
            theme_words = evaluation.get("theme_words", [])
            if not theme_words:
                continue
                
            with_themes += 1
            
            # Extract topics from the pair (stored in metadata or inferred)
            # We need to find which pair this evaluation was for
            # The cache stores by hash, so we need to look at bridge nodes
            pass
            
        except (json.JSONDecodeError, KeyError):
            continue
    
    # Better approach: scan bridge nodes which have topic info + score
    bridges = sm.list_by_tag("bridge")
    seen_pairs = set()
    
    for b in bridges:
        meta = b.get("metadata", {})
        topics = meta.get("bridged_topics", [])
        if len(topics) != 2:
            continue
            
        pair_key = tuple(sorted(topics))
        if pair_key in seen_pairs:
            continue
        seen_pairs.add(pair_key)
        
        score = meta.get("relevancy_score", 0)
        if score < BRIDGE_THRESHOLD:
            continue
        
        # Find the cached evaluation for this pair to get theme_words
        eval_hash = meta.get("evaluation_hash")
        theme_words = []
        
        # Search cache for matching evaluation
        for mem in cache_memories:
            try:
                evaluation = json.loads(mem.get("content", "{}"))
                # Check if this has theme_words and matches our score
                if abs(evaluation.get("relevancy_score", 0) - score) < 0.01:
                    theme_words = evaluation.get("theme_words", [])
                    if theme_words:
                        break
            except:
                continue
        
        # Aggregate themes
        for theme in theme_words:
            theme_lower = theme.lower().strip()
            if theme_lower:
                themes[theme_lower]["topics"].update(topics)
                themes[theme_lower]["pairs"].append(pair_key)
                themes[theme_lower]["score_sum"] += score
    
    return {
        "themes": dict(themes),
        "total_evaluations": len(seen_pairs),
        "pairs_with_themes": with_themes
    }


def get_existing_theme_syntheses(sm: SemanticMemory) -> set:
    """Find which themes already have synthesis documents."""
    syntheses = sm.list_by_tag("synthesis")
    theme_tags = set()
    
    for s in syntheses:
        tags = s.get("tags", [])
        for tag in tags:
            if tag.startswith("theme:"):
                theme_tags.add(tag[6:].lower())
    
    return theme_tags


def show_themes(sm: SemanticMemory):
    """Show theme clusters and synthesis debt."""
    agg = aggregate_themes(sm)
    themes = agg["themes"]
    
    if not themes:
        print("No themes found. Need to run evaluation first...")
        print("Running exhaustive bridge evaluation...\n")
        exhaustive_bridge(sm)
        agg = aggregate_themes(sm)
        themes = agg["themes"]
    
    if not themes:
        print("Still no themes. Check that syntheses exist for topics.")
        return
    
    # Get existing theme syntheses
    existing = get_existing_theme_syntheses(sm)
    
    # Sort themes by number of topics (most connected first)
    sorted_themes = sorted(themes.items(), key=lambda x: len(x[1]["topics"]), reverse=True)
    
    print(f"{'='*60}")
    print("THEME CLUSTERS")
    print(f"{'='*60}\n")
    
    pending_themes = []
    completed_themes = []
    
    for theme, data in sorted_themes:
        topics = sorted(data["topics"])
        if len(topics) < 2:
            continue  # Skip single-topic themes
            
        is_synthesized = theme in existing
        status = "✓" if is_synthesized else "○"
        
        entry = {
            "theme": theme,
            "topics": topics,
            "pairs": len(data["pairs"]),
            "avg_score": data["score_sum"] / len(data["pairs"]) if data["pairs"] else 0
        }
        
        if is_synthesized:
            completed_themes.append(entry)
        else:
            pending_themes.append(entry)
    
    # Show pending first (the debt)
    if pending_themes:
        print("PENDING (need synthesis):\n")
        for entry in pending_themes:
            print(f"  ○ {entry['theme']} ({len(entry['topics'])} topics)")
            print(f"    {', '.join(entry['topics'])}")
            print()
    
    if completed_themes:
        print("COMPLETED:\n")
        for entry in completed_themes:
            print(f"  ✓ {entry['theme']} ({len(entry['topics'])} topics)")
            print(f"    {', '.join(entry['topics'])}")
            print()
    
    # Show synthesis debt summary
    print(f"{'='*60}")
    print("SYNTHESIS DEBT")
    print(f"{'='*60}\n")
    
    if pending_themes:
        print(f"  {len(pending_themes)} theme(s) need synthesis\n")
        
        # Show how to clear for the top theme
        top = pending_themes[0]
        topics_str = ' '.join(top['topics'])
        print(f"  To clear '{top['theme']}':")
        print(f"    py recollect.py opus {topics_str}")
        print(f"    py remember.py opus - \"@G {top['theme']}-synthesis opus {datetime.now().strftime('%Y-%m-%d')}\"")
        print(f"       N i1 I '[insight weaving these topics]'")
        print(f"       tags: synthesis, theme:{top['theme']}")
        for t in top['topics']:
            print(f"             topic:{t}")
    else:
        print("  All themes synthesized! ✓")
    
    print()
    return {"pending": pending_themes, "completed": completed_themes}


def show_existing_bridges(sm: SemanticMemory):
    """Show all existing bridge nodes (raw view)."""
    bridges = sm.list_by_tag("bridge")
    
    if not bridges:
        print("No bridges found. Run with no args to discover themes.")
        return
    
    print(f"Found {len(bridges)} bridge nodes:\n")
    
    # Group by bridge
    by_bridge = {}
    for b in bridges:
        meta = b.get("metadata", {})
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
    
    # Use shared enclave for bridge analysis - no fallback
    if not agent.shared_enclave:
        print(f"Error: No shared_enclave configured for {agent_id}", file=sys.stderr)
        sys.exit(1)
    
    enclave_dir = Path(agent.shared_enclave)
    passphrase = os.getenv('SHARED_ENCLAVE_KEY')
    
    if not passphrase:
        print("Error: Set SHARED_ENCLAVE_KEY in .env", file=sys.stderr)
        sys.exit(1)
    
    sm = SemanticMemory(enclave_dir)
    sm.unlock(passphrase)
    
    # Parse args
    if len(sys.argv) >= 3:
        arg = sys.argv[2]
        if arg == "--refresh":
            # Re-evaluate all pairs, then show themes
            exhaustive_bridge(sm)
            print("\n")
            show_themes(sm)
        elif arg == "--raw":
            # Show raw bridges without theme aggregation
            show_existing_bridges(sm)
        else:
            print(__doc__)
            sys.exit(1)
    else:
        # Default: show themes (run exhaustive if needed)
        show_themes(sm)


if __name__ == "__main__":
    main()
