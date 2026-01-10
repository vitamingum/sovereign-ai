#!/usr/bin/env python3
"""
explore.py - Question-driven knowledge traversal.

Start from any question or topic, find relevant synthesis,
then walk bridges to discover connected understanding.

Usage:
    py explore opus "why does passphrase matter?"
    py explore opus --topic cryptography
    py explore opus --topic cryptography --depth 2
    py explore opus --clusters

The key insight: bridges connect isolated understanding.
Following them reveals how everything fits together.
"""

import sys
import os
import json
from pathlib import Path
from typing import Optional, List, Set, Dict
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from enclave_shared.config import get_agent_or_raise
from enclave_shared.semantic_memory import SemanticMemory


def get_passphrase(agent_name: str) -> str:
    """Get passphrase from environment."""
    from dotenv import load_dotenv
    load_dotenv()
    key = f"ENCLAVE_{agent_name.upper()}_KEY"
    passphrase = os.getenv(key)
    if not passphrase:
        raise ValueError(f"Set {key} environment variable")
    return passphrase


def get_all_syntheses(sm: SemanticMemory) -> Dict[str, str]:
    """Get all synthesis content keyed by topic."""
    syntheses = {}
    for mem in sm.list_by_tag("synthesis"):
        for tag in mem.get("tags", []):
            if tag.startswith("topic:"):
                topic = tag.replace("topic:", "")
                syntheses[topic] = mem.get("content", "")
    return syntheses


def get_all_bridges(sm: SemanticMemory) -> List[Dict]:
    """Get all bridge metadata."""
    bridges = []
    seen = set()
    
    for mem in sm.list_by_tag("bridge"):
        meta = mem.get("metadata", {})
        bridged = tuple(sorted(meta.get("bridged_topics", [])))
        if bridged and bridged not in seen:
            seen.add(bridged)
            bridges.append({
                "topics": list(bridged),
                "relevancy": meta.get("relevancy_score", 0),
                "connection_type": meta.get("connection_type", "unknown")
            })
    
    return bridges


def get_bridges_for_topic(sm: SemanticMemory, topic: str) -> List[Dict]:
    """Get all bridges involving a specific topic."""
    bridges = []
    for mem in sm.list_by_tag("bridge"):
        meta = mem.get("metadata", {})
        topics = meta.get("bridged_topics", [])
        if topic in topics:
            other = [t for t in topics if t != topic]
            if other:
                bridges.append({
                    "connected_to": other[0],
                    "relevancy": meta.get("relevancy_score", 0),
                    "connection_type": meta.get("connection_type", "unknown")
                })
    
    # Dedupe and sort by relevancy
    seen = set()
    unique = []
    for b in sorted(bridges, key=lambda x: -x["relevancy"]):
        if b["connected_to"] not in seen:
            seen.add(b["connected_to"])
            unique.append(b)
    
    return unique


def walk_bridges(sm: SemanticMemory, start_topic: str, depth: int = 2) -> Dict[str, Set[str]]:
    """Walk bridge graph from a starting topic to find connected clusters.
    
    Returns dict mapping topic -> set of topics reachable within depth.
    """
    visited = set([start_topic])
    current_layer = set([start_topic])
    layers = {0: {start_topic}}
    
    for d in range(1, depth + 1):
        next_layer = set()
        for topic in current_layer:
            bridges = get_bridges_for_topic(sm, topic)
            for bridge in bridges:
                connected = bridge["connected_to"]
                if connected not in visited:
                    next_layer.add(connected)
                    visited.add(connected)
        
        if next_layer:
            layers[d] = next_layer
        current_layer = next_layer
    
    return layers


def detect_clusters(sm: SemanticMemory) -> List[Set[str]]:
    """Find connected components in the bridge graph."""
    bridges = get_all_bridges(sm)
    
    # Build adjacency
    adj = defaultdict(set)
    all_topics = set()
    for b in bridges:
        t1, t2 = b["topics"]
        adj[t1].add(t2)
        adj[t2].add(t1)
        all_topics.add(t1)
        all_topics.add(t2)
    
    # BFS for components
    visited = set()
    clusters = []
    
    for topic in all_topics:
        if topic not in visited:
            cluster = set()
            queue = [topic]
            while queue:
                t = queue.pop(0)
                if t not in visited:
                    visited.add(t)
                    cluster.add(t)
                    queue.extend(adj[t] - visited)
            clusters.append(cluster)
    
    return sorted(clusters, key=lambda x: -len(x))


def search_syntheses(sm: SemanticMemory, query: str, limit: int = 5) -> List[Dict]:
    """Semantic search across all syntheses."""
    results = sm.recall(query, limit=limit, tags=["synthesis"])
    return [{"topic": extract_topic(r), "content": r.get("content", ""), "score": r.get("score", 0)} 
            for r in results]


def extract_topic(mem: dict) -> str:
    """Extract topic name from a synthesis memory."""
    for tag in mem.get("tags", []):
        if tag.startswith("topic:"):
            return tag.replace("topic:", "")
    # Fallback: try to extract from content
    content = mem.get("content", "")
    if "@G " in content:
        start = content.find("@G ") + 3
        end = content.find(" ", start)
        if end == -1:
            end = content.find(";", start)
        return content[start:end].replace("-synthesis", "")
    return "unknown"


def format_synthesis_brief(content: str, max_len: int = 300) -> str:
    """Create a brief summary from SIF content."""
    # Extract principles (P nodes) as they're most insight-dense
    principles = []
    for part in content.split("' N "):
        if part.strip().startswith("p") or " P '" in part:
            # Extract the content after type marker
            if "P '" in part:
                start = part.find("P '") + 3
                end = part.find("'", start)
                if end > start:
                    principles.append(part[start:end])
    
    if principles:
        return " | ".join(principles[:3])
    
    return content[:max_len] + "..." if len(content) > max_len else content


def explore_topic(sm: SemanticMemory, topic: str, depth: int = 2):
    """Explore a topic and its bridge connections."""
    syntheses = get_all_syntheses(sm)
    
    if topic not in syntheses:
        print(f"✗ No synthesis found for '{topic}'")
        print(f"  Available: {', '.join(sorted(syntheses.keys())[:10])}...")
        return
    
    print(f"\n{'='*60}")
    print(f"EXPLORING: {topic}")
    print(f"{'='*60}")
    
    # Show the synthesis
    content = syntheses[topic]
    print(f"\n📝 Core synthesis:")
    print(f"   {format_synthesis_brief(content)}")
    
    # Walk bridges
    layers = walk_bridges(sm, topic, depth)
    
    if len(layers) > 1:
        print(f"\n🌉 Connected topics (depth={depth}):")
        for d, topics in layers.items():
            if d == 0:
                continue
            prefix = "  " * d + "→"
            for t in sorted(topics):
                bridges = get_bridges_for_topic(sm, t)
                rel = next((b["relevancy"] for b in bridges if b["connected_to"] in layers.get(d-1, set())), 0)
                ctype = next((b["connection_type"] for b in bridges if b["connected_to"] in layers.get(d-1, set())), "")
                print(f"   {prefix} {t} ({rel:.2f} {ctype})")
                if t in syntheses:
                    print(f"      {format_synthesis_brief(syntheses[t], 100)}")
    else:
        print(f"\n🏝️ No bridges found from this topic (island)")
        bridges = get_bridges_for_topic(sm, topic)
        if bridges:
            print(f"   Direct connections: {[b['connected_to'] for b in bridges[:5]]}")


def explore_question(sm: SemanticMemory, question: str, depth: int = 2):
    """Answer a question by finding relevant syntheses and following bridges."""
    print(f"\n{'='*60}")
    print(f"QUESTION: {question}")
    print(f"{'='*60}")
    
    # Find relevant syntheses
    results = search_syntheses(sm, question, limit=3)
    
    if not results:
        print("✗ No relevant syntheses found")
        return
    
    syntheses = get_all_syntheses(sm)
    
    for i, r in enumerate(results):
        topic = r["topic"]
        print(f"\n📌 Match {i+1}: {topic} (score: {r['score']:.3f})")
        print(f"   {format_synthesis_brief(r['content'], 200)}")
        
        # Follow bridges from this topic
        layers = walk_bridges(sm, topic, depth)
        if len(layers) > 1:
            connected = []
            for d, topics in layers.items():
                if d > 0:
                    connected.extend(topics)
            print(f"   → Connected: {', '.join(sorted(connected)[:5])}")


def show_clusters(sm: SemanticMemory):
    """Show all knowledge clusters and orphan topics."""
    clusters = detect_clusters(sm)
    syntheses = get_all_syntheses(sm)
    
    # Find orphans (topics with synthesis but no bridges)
    bridged = set()
    for cluster in clusters:
        bridged.update(cluster)
    
    orphans = set(syntheses.keys()) - bridged
    
    print(f"\n{'='*60}")
    print("KNOWLEDGE CLUSTERS")
    print(f"{'='*60}")
    
    for i, cluster in enumerate(clusters):
        print(f"\n🌐 Cluster {i+1} ({len(cluster)} topics):")
        for topic in sorted(cluster):
            bridges = get_bridges_for_topic(sm, topic)
            conn_count = len(bridges)
            print(f"   • {topic} ({conn_count} connections)")
    
    if orphans:
        print(f"\n🏝️ ORPHAN TOPICS (no bridges):")
        for topic in sorted(orphans):
            print(f"   • {topic}")
        print(f"\n   ⚠️ {len(orphans)} topics have no cross-connections")
        print(f"   Consider: py bridge opus <orphan> <another-topic>")


def show_stats(sm: SemanticMemory):
    """Show bridge statistics."""
    bridges = get_all_bridges(sm)
    syntheses = get_all_syntheses(sm)
    clusters = detect_clusters(sm)
    
    bridged = set()
    for cluster in clusters:
        bridged.update(cluster)
    orphans = set(syntheses.keys()) - bridged
    
    print(f"\n📊 Bridge Statistics:")
    print(f"   Syntheses: {len(syntheses)}")
    print(f"   Bridges: {len(bridges)}")
    print(f"   Clusters: {len(clusters)}")
    print(f"   Orphans: {len(orphans)}")
    
    if bridges:
        avg_rel = sum(b["relevancy"] for b in bridges) / len(bridges)
        print(f"   Avg relevancy: {avg_rel:.2f}")
        
        # Connection type distribution
        types = defaultdict(int)
        for b in bridges:
            types[b["connection_type"]] += 1
        print(f"   Connection types:")
        for ctype, count in sorted(types.items(), key=lambda x: -x[1]):
            print(f"      {ctype}: {count}")


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_name = sys.argv[1]
    try:
        agent = get_agent_or_raise(agent_name)
    except Exception as e:
        print(f"✗ {e}")
        sys.exit(1)
    
    enclave_dir = Path(f"enclave_{agent.name.lower()}")
    passphrase = get_passphrase(agent.name)
    
    sm = SemanticMemory(enclave_dir)
    sm.unlock(passphrase)
    
    # Parse arguments
    if len(sys.argv) == 2:
        # Just show stats
        show_stats(sm)
        sys.exit(0)
    
    if sys.argv[2] == "--clusters":
        show_clusters(sm)
        sys.exit(0)
    
    if sys.argv[2] == "--topic":
        if len(sys.argv) < 4:
            print("Usage: py explore <agent> --topic <topic> [--depth N]")
            sys.exit(1)
        topic = sys.argv[3]
        depth = 2
        if "--depth" in sys.argv:
            idx = sys.argv.index("--depth")
            depth = int(sys.argv[idx + 1])
        explore_topic(sm, topic, depth)
        sys.exit(0)
    
    # Default: treat as question
    question = " ".join(sys.argv[2:])
    explore_question(sm, question)


if __name__ == "__main__":
    main()
