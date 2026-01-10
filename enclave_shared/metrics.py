"""
Sovereign AI Enclave - Metrics & Telemetry

Calculates 'Enclave Entropy' and other sovereignty metrics.
"""

import os
import sys
import time
import traceback
from pathlib import Path
from datetime import datetime, timezone, timedelta

# Add root to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from enclave_shared.config import get_agent_or_raise
from enclave_shared.hardware import get_enclave
from enclave_shared.semantic_memory import SemanticMemory

def calculate_synthesis(agent_id: str) -> float:
    """
    Calculate Synthesis Potential.
    
    Synthesis = sum(1 - similarity(u, v)) for all edges (u, v).
    
    This measures the 'tension' or 'distance' bridged by connections.
    High synthesis means the agent is connecting disparate concepts.
    Survival pulls away from destruction. Synthesis pulls toward creation.
    """
    try:
        from wake import load_passphrase
        import json
        import numpy as np
        
        shared_enclave, private_enclave, shared_passphrase, private_passphrase = load_passphrase(agent_id)
        memory = SemanticMemory(enclave_path=shared_enclave)
        if not memory.unlock(shared_passphrase):
            return 0.0
            
        # Ensure we can use embeddings (requires sentence-transformers)
        # We access the private helper to check availability
        from enclave_shared.semantic_memory import _ensure_embeddings
        if not _ensure_embeddings():
            return 0.0

        log_file = Path(enclave_dir) / "storage" / "private" / "semantic_memories.jsonl"
        if not log_file.exists():
            return 0.0
            
        node_embeddings = {} # node_id -> np.array
        edges = [] # list of (source, target)
        
        with open(log_file, 'r', encoding='utf-8') as f:
            for line in f:
                if not line.strip(): continue
                try:
                    entry = json.loads(line)
                    if "sif_node" not in entry.get("tags", []):
                        continue
                    
                    if "embedding" not in entry:
                        continue
                        
                    # Decrypt embedding
                    emb = memory._decrypt_embedding(entry["embedding"])
                    
                    # Decrypt metadata to get node_id and edges
                    content_nonce = bytes.fromhex(entry["content_nonce"])
                    content_ciphertext = bytes.fromhex(entry["content"])
                    decrypted_bytes = memory._decrypt(
                        content_nonce, content_ciphertext, memory._encryption_key
                    )
                    
                    # Handle potential legacy format or JSON errors
                    try:
                        payload = json.loads(decrypted_bytes.decode())
                        if isinstance(payload, dict):
                            meta = payload.get("meta", {})
                        else:
                            meta = {}
                    except:
                        continue

                    node_id = meta.get("node_id")
                    
                    if node_id:
                        node_embeddings[node_id] = emb
                        
                        # Collect OUTGOING edges only to avoid double counting
                        # Format varies: "edges" (old ingest_graph) or "outgoing_edges" (current)
                        node_edges = meta.get("edges", [])
                        for e in node_edges:
                            if e.get("direction") == "out":
                                edges.append((node_id, e["target"]))
                        
                        # Current format: outgoing_edges as [[relation, target], ...]
                        outgoing = meta.get("outgoing_edges", [])
                        for e in outgoing:
                            if isinstance(e, list) and len(e) >= 2:
                                edges.append((node_id, e[1]))
                                
                except Exception:
                    continue
        
        if not edges:
            return 0.0
            
        total_potential = 0.0
        
        for u, v in edges:
            if u in node_embeddings and v in node_embeddings:
                # Cosine similarity (embeddings are normalized by sentence-transformers)
                u_vec = node_embeddings[u]
                v_vec = node_embeddings[v]
                
                # Dot product of normalized vectors is cosine similarity
                sim = float(np.dot(u_vec, v_vec))
                
                # Clamp for numerical stability
                sim = max(-1.0, min(1.0, sim))
                
                # Distance = 1 - Similarity
                # If sim is 1.0 (identical), potential is 0.
                # If sim is 0.0 (orthogonal), potential is 1.
                dist = 1.0 - sim
                total_potential += dist
                
        return total_potential
        
    except Exception as e:
        # Memory: "Returns 0.0 on any exception - silent failure masks real problems"
        print(f"[metrics] calculate_synthesis failed: {e}", file=sys.stderr)
        return 0.0


def calculate_synthesis_gaps(agent_id: str) -> dict:
    """
    Calculate synthesis gaps based on THEMES, not bridge pairs.
    
    Theme-based model:
      - Bridge evaluations extract theme_words (abstract nouns like "resilience")
      - Themes aggregate across pairs → "resilience" spans [backup, risk, crypto]
      - Gaps = themes with 2+ topics that don't have a synthesis tagged theme:<name>
    
    This makes synthesis tractable: O(themes) not O(pairs).
    
    Returns dict with:
      - themes_total: distinct themes found in evaluations
      - themes_synthesized: themes with existing synthesis
      - themes_pending: themes needing synthesis (the debt)
      - pending_themes: list of {name, topics} needing synthesis
      - total: count of pending themes (for wake.py threshold check)
    """
    import json
    from collections import defaultdict
    
    try:
        from wake import load_passphrase
        shared_enclave, private_enclave, shared_passphrase, private_passphrase = load_passphrase(agent_id)
        memory = SemanticMemory(enclave_path=shared_enclave)
        if not memory.unlock(shared_passphrase):
            return {'themes_total': 0, 'themes_synthesized': 0, 'themes_pending': 0, 'pending_themes': [], 'total': 0}
        
        # --- AGGREGATE THEMES FROM BRIDGE CACHE ---
        cache_memories = memory.list_by_tag("bridge_cache")
        bridges = memory.list_by_tag("bridge")
        
        # Build map: pair -> score from bridge nodes
        pair_scores = {}
        for b in bridges:
            meta = b.get('metadata', {})
            topics = meta.get('bridged_topics', [])
            if len(topics) == 2:
                pair_key = tuple(sorted(topics))
                pair_scores[pair_key] = meta.get('relevancy_score', 0)
        
        # Aggregate themes from cache
        themes = defaultdict(lambda: {"topics": set(), "score_sum": 0.0, "pair_count": 0})
        
        for mem in cache_memories:
            try:
                evaluation = json.loads(mem.get("content", "{}"))
                score = evaluation.get("relevancy_score", 0)
                if score < 0.6:  # BRIDGE_THRESHOLD
                    continue
                
                theme_words = evaluation.get("theme_words", [])
                if not theme_words:
                    continue
                
                # Find which pair this evaluation was for by matching score
                # (imperfect but works with single-digit precision)
                matched_pair = None
                for pair, pair_score in pair_scores.items():
                    if abs(pair_score - score) < 0.01:
                        matched_pair = pair
                        break
                
                if matched_pair:
                    for theme in theme_words:
                        theme_lower = theme.lower().strip()
                        if theme_lower:
                            themes[theme_lower]["topics"].update(matched_pair)
                            themes[theme_lower]["score_sum"] += score
                            themes[theme_lower]["pair_count"] += 1
                            
            except (json.JSONDecodeError, KeyError):
                continue
        
        # Filter to themes with 2+ topics
        valid_themes = {k: v for k, v in themes.items() if len(v["topics"]) >= 2}
        
        # --- FIND EXISTING THEME SYNTHESES ---
        syntheses = memory.list_by_tag("synthesis")
        synthesized_themes = set()
        
        for s in syntheses:
            tags = s.get("metadata", {}).get("tags", [])
            for tag in tags:
                if tag.startswith("theme:"):
                    synthesized_themes.add(tag[6:].lower())
        
        # --- CALCULATE DEBT ---
        pending_themes = []
        for theme_name, data in valid_themes.items():
            if theme_name not in synthesized_themes:
                pending_themes.append({
                    "name": theme_name,
                    "topics": sorted(list(data["topics"])),
                    "pair_count": data["pair_count"]
                })
        
        # Sort by number of topics (highest debt first)
        pending_themes.sort(key=lambda x: len(x["topics"]), reverse=True)
        
        return {
            'themes_total': len(valid_themes),
            'themes_synthesized': len(synthesized_themes & set(valid_themes.keys())),
            'themes_pending': len(pending_themes),
            'pending_themes': pending_themes,
            'total': len(pending_themes)  # For backwards compatibility
        }
        
    except Exception as e:
        return {'themes_total': 0, 'themes_synthesized': 0, 'themes_pending': 0, 'pending_themes': [], 'total': 0, 'error': str(e)}


def calculate_cross_agent_gaps(agent_id: str, memory: SemanticMemory) -> dict:
    """
    Calculate what files OTHER agents have understood that THIS agent hasn't.
    
    For shared enclaves - forces agents to catch up to each other's understanding.
    
    Returns:
        {
            'my_files': set of files this agent understands,
            'partner_files': {partner_id: set of files they understand},
            'my_gaps': set of files I need to understand,
            'gap_count': int
        }
    """
    from enclave_shared.config import get_enclave_partners, AGENTS
    
    partners = get_enclave_partners(agent_id)
    if not partners:
        return {'my_files': set(), 'partner_files': {}, 'my_gaps': set(), 'gap_count': 0}
    
    # Get all memories
    all_mems = memory.list_all(limit=5000)
    
    # Index files by creator
    files_by_agent = {}
    for mem in all_mems:
        creator = mem.get('metadata', {}).get('creator', 'unknown')
        target = mem.get('metadata', {}).get('target_path', '')
        node_type = mem.get('metadata', {}).get('node_type', '')
        
        # Only count WHY-type understanding
        if target and node_type in ['Why', 'Design_Decision', 'Rejected_Alternative',
                                     'Gotcha', 'Failure_Mode', 'Assumption', 'Design',
                                     'Purpose', 'Component']:
            if creator not in files_by_agent:
                files_by_agent[creator] = set()
            files_by_agent[creator].add(target)
    
    my_files = files_by_agent.get(agent_id, set())
    
    # Collect all files partners understand
    partner_files = {}
    all_partner_files = set()
    for partner in partners:
        pfiles = files_by_agent.get(partner.id, set())
        partner_files[partner.id] = pfiles
        all_partner_files.update(pfiles)
    
    # My gaps = files partners have that I don't (only if file still exists)
    from pathlib import Path
    project_root = Path(__file__).parent.parent
    my_gaps = set()
    for f in (all_partner_files - my_files):
        # Check if file exists at project root
        if (project_root / f).exists():
            my_gaps.add(f)
    
    return {
        'my_files': my_files,
        'partner_files': partner_files,
        'my_gaps': my_gaps,
        'gap_count': len(my_gaps)
    }


if __name__ == "__main__":
    if len(sys.argv) > 1:
        gaps = calculate_synthesis_gaps(sys.argv[1])
        print(f"Synthesis gaps for {sys.argv[1]}: {gaps['total']} themes pending")
    else:
        print("Usage: py -m enclave.metrics <agent_id>")
