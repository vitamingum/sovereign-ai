"""
Sovereign AI Enclave - Metrics & Telemetry

Calculates 'Enclave Entropy' and other sovereignty metrics.
"""

import os
import sys
import time
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
        
        enclave_dir, passphrase = load_passphrase(agent_id)
        memory = SemanticMemory(enclave_path=enclave_dir)
        if not memory.unlock(passphrase):
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
                        # (ingest_graph stores both in and out)
                        node_edges = meta.get("edges", [])
                        for e in node_edges:
                            if e.get("direction") == "out":
                                edges.append((node_id, e["target"]))
                                
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
        
    except Exception:
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
    Calculate synthesis debt at file and topic levels.
    
    Returns dict with:
      - file_debt: count of files without deep understanding
      - topic_debt: count of core topics without synthesis
      - total: file_debt + topic_debt
    
    This is fast - pure memory queries, no LLM needed.
    """
    from collections import defaultdict
    
    try:
        from wake import load_passphrase
        enclave_dir, passphrase = load_passphrase(agent_id)
        memory = SemanticMemory(enclave_path=enclave_dir)
        if not memory.unlock(passphrase):
            return {'file_debt': 0, 'topic_debt': 0, 'total': 0}
        
        # --- FILE DEBT ---
        # Count files without deep understanding (WHY nodes)
        root = Path(__file__).parent.parent
        all_files = set()
        
        # Core Python files
        for p in root.glob('*.py'):
            if not p.name.startswith(('generated_', 'test_', 'debug_')):
                all_files.add(p.name)
        
        # Enclave files
        enclave = root / 'enclave'
        if enclave.exists():
            for p in enclave.glob('*.py'):
                if not p.name.startswith('test'):
                    all_files.add(f"enclave/{p.name}")
        
        # Get files with understanding
        all_mems = memory.list_all(limit=1000)
        files_with_understanding = set()
        
        for mem in all_mems:
            target = mem.get('metadata', {}).get('target_path', '')
            node_type = mem.get('metadata', {}).get('node_type', '')
            
            if target:
                filename = Path(target).name
                # Only count if it has WHY-type nodes
                if node_type in ['Why', 'Design_Decision', 'Rejected_Alternative',
                               'Gotcha', 'Failure_Mode', 'Assumption', 'Design']:
                    files_with_understanding.add(filename)
        
        file_debt = len(all_files - files_with_understanding)
        
        # --- TOPIC DEBT ---
        CORE_TOPICS = [
            'semantic memory', 'graph memory', 'encryption', 'cryptography',
            'SIF format', 'messaging', 'backup', 'succession',
            'think', 'remember', 'recollect', 'wake', 'mirror', 'dream', 'goal', 'reflect',
            'intentions', 'agency', 'authenticity', 'identity', 'sovereignty',
            'blind spots', 'continuity', 'entropy',
            'config', 'risk', 'hardware', 'LLM', 'metrics',
        ]
        
        # Get existing syntheses
        syntheses = memory.list_by_tag('synthesis', limit=100)
        synthesized_topics = set()
        
        for s in syntheses:
            content = s.get('content', '')
            if '@G ' in content:
                start = content.find('@G ') + 3
                end = content.find(' ', start)
                if end == -1:
                    end = content.find(';', start)
                if end > start:
                    slug = content[start:end]
                    topic = slug.replace('-synthesis', '').replace('-', ' ')
                    synthesized_topics.add(topic.lower())
        
        topic_debt = 0
        for topic in CORE_TOPICS:
            topic_lower = topic.lower()
            # Check if any synthesis covers this topic
            covered = any(
                set(topic_lower.split()) & set(st.split())
                for st in synthesized_topics
            )
            if not covered:
                topic_debt += 1
        
        return {
            'file_debt': file_debt,
            'topic_debt': topic_debt,
            'total': file_debt + topic_debt
        }
        
    except Exception as e:
        return {'file_debt': 0, 'topic_debt': 0, 'total': 0, 'error': str(e)}


if __name__ == "__main__":
    if len(sys.argv) > 1:
        print(generate_dashboard_sif(sys.argv[1]))
    else:
        print("Usage: py -m enclave.metrics <agent_id>")
