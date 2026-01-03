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

from enclave.config import get_agent_or_raise
from enclave.hardware import get_enclave
from enclave.semantic_memory import SemanticMemory

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
        from enclave.semantic_memory import _ensure_embeddings
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

def get_key_security_score(agent_id: str) -> float:
    """
    Score 0.0-1.0 based on key storage.
    1.0 = Hardware Enclave (Sealed)
    0.5 = Environment Variable
    0.0 = Missing/Unknown
    """
    agent = get_agent_or_raise(agent_id)
    enclave_dir = os.environ.get(f'{agent.env_prefix}_DIR') or agent.enclave
    key_file = Path(enclave_dir) / "storage" / "private" / "key.sealed"
    
    if key_file.exists():
        return 1.0
    elif os.environ.get(f'{agent.env_prefix}_KEY') or os.environ.get('SOVEREIGN_PASSPHRASE'):
        return 0.5
    else:
        return 0.0

def get_backup_freshness_score(agent_id: str) -> float:
    """
    Score 0.0-1.0 based on time since last backup.
    1.0 = < 1 hour
    0.8 = < 24 hours
    0.5 = < 1 week
    0.0 = > 1 week or none
    """
    # TODO: Implement actual backup check. For now, check git log timestamp?
    # Assuming git push is the backup mechanism for now.
    try:
        # This is a heuristic. In a real enclave, we'd check the opaque storage.
        # For now, we return a placeholder high score if we are running.
        return 0.9 
    except:
        return 0.0

def calculate_enclave_entropy(agent_id: str) -> float:
    """
    Calculate the 'Enclave Entropy' (Risk).
    Lower is better (0.0 = Safe, 1.0 = Maximum Entropy/Risk).
    
    Formula: 1.0 - (KeySecurity * 0.6 + BackupFreshness * 0.4)
    """
    key_score = get_key_security_score(agent_id)
    backup_score = get_backup_freshness_score(agent_id)
    
    stability = (key_score * 0.6) + (backup_score * 0.4)
    entropy = 1.0 - stability
    return round(entropy, 3)

def generate_dashboard_sif(agent_id: str) -> str:
    """Generate a SIF graph representing the current metrics."""
    entropy = calculate_enclave_entropy(agent_id)
    key_score = get_key_security_score(agent_id)
    
    timestamp = datetime.now(timezone.utc).isoformat()
    graph_id = f"metrics-{agent_id}-{int(time.time())}"
    
    lines = []
    lines.append(f"@G {graph_id} {agent_id} {timestamp}")
    lines.append(f'N self Agent "{agent_id}"')
    lines.append(f'N m1 Metric "Enclave Entropy"')
    lines.append(f'N v1 Value "{entropy}"')
    lines.append(f'E self has_metric m1')
    lines.append(f'E m1 has_value v1')
    
    if entropy > 0.5:
        lines.append(f'N risk Concept "High Risk"')
        lines.append(f'E v1 implies risk')
    else:
        lines.append(f'N safety Concept "Stable State"')
        lines.append(f'E v1 implies safety')
        
    return "\n".join(lines)


def calculate_synthesis_debt(agent_id: str) -> dict:
    """
    Calculate synthesis debt based on THEMES, not bridge pairs.
    
    Theme-based model:
      - Bridge evaluations extract theme_words (abstract nouns like "resilience")
      - Themes aggregate across pairs → "resilience" spans [backup, risk, crypto]
      - Debt = themes with 2+ topics that don't have a synthesis tagged theme:<name>
    
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


def calculate_cross_agent_debt(agent_id: str, memory: SemanticMemory) -> dict:
    """
    Calculate what files OTHER agents have understood that THIS agent hasn't.
    
    For shared enclaves - forces agents to catch up to each other's understanding.
    
    Returns:
        {
            'my_files': set of files this agent understands,
            'partner_files': {partner_id: set of files they understand},
            'my_debt': set of files I need to understand,
            'debt_count': int
        }
    """
    from enclave.config import get_enclave_partners, AGENTS
    
    partners = get_enclave_partners(agent_id)
    if not partners:
        return {'my_files': set(), 'partner_files': {}, 'my_debt': set(), 'debt_count': 0}
    
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
    
    # My debt = files partners have that I don't (only if file still exists)
    from pathlib import Path
    project_root = Path(__file__).parent.parent
    my_debt = set()
    for f in (all_partner_files - my_files):
        # Check if file exists at project root
        if (project_root / f).exists():
            my_debt.add(f)
    
    return {
        'my_files': my_files,
        'partner_files': partner_files,
        'my_debt': my_debt,
        'debt_count': len(my_debt)
    }


if __name__ == "__main__":
    if len(sys.argv) > 1:
        print(generate_dashboard_sif(sys.argv[1]))
    else:
        print("Usage: py -m enclave.metrics <agent_id>")
