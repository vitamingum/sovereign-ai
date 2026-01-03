#!/usr/bin/env python3
"""
merge_enclaves.py - Merge two agent enclaves into a shared enclave.

Usage:
    py merge_enclaves.py <agent1> <agent2> [--target enclave_shared]
    
Example:
    py merge_enclaves.py opus gemini
    
This will:
1. Export memories from both agents (decrypting with their keys)
2. Prefix graph_ids with agent name for disambiguation
3. Merge into shared enclave's semantic_memories.jsonl
4. Copy identity keys to shared enclave
"""

import sys
import os
import json
import shutil
from pathlib import Path
from datetime import datetime, timezone
from typing import List, Dict, Set

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise, AGENTS
from enclave.semantic_memory import SemanticMemory


def load_passphrase(agent_id: str) -> str:
    """Load passphrase from env or .env file."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    
    passphrase = os.environ.get(f'{prefix}_KEY')
    if passphrase:
        return passphrase
    
    env_file = Path(__file__).parent / '.env'
    if env_file.exists():
        with open(env_file, 'r') as f:
            for line in f:
                line = line.strip()
                if line.startswith(f'{prefix}_KEY='):
                    return line.split('=', 1)[1]
    
    raise ValueError(f"No passphrase found for {agent_id}. Set {prefix}_KEY in environment or .env")


def export_memories(agent_id: str, passphrase: str) -> List[dict]:
    """Export all memories from an agent's enclave, decrypted."""
    agent = get_agent_or_raise(agent_id)
    enclave_path = Path(__file__).parent / agent.enclave
    
    mem = SemanticMemory(str(enclave_path))
    mem.unlock(passphrase)
    
    # Get all memories
    memories = mem.list_all(limit=None)
    
    print(f"  Exported {len(memories)} memories from {agent_id}")
    return memories


def prefix_graph_ids(memories: List[dict], agent_id: str) -> List[dict]:
    """Prefix graph_ids with agent name for disambiguation."""
    prefixed = []
    
    for mem in memories:
        new_mem = mem.copy()
        
        # Prefix graph_id in metadata
        if 'metadata' in new_mem and 'graph_id' in new_mem['metadata']:
            old_id = new_mem['metadata']['graph_id']
            if not old_id.startswith(f'{agent_id}:'):
                new_mem['metadata']['graph_id'] = f"{agent_id}:{old_id}"
        
        # Prefix graph_id in tags
        if 'tags' in new_mem:
            new_tags = []
            for tag in new_mem['tags']:
                # Don't prefix common tags, only graph-like IDs
                if '-understanding' in tag or '-synthesis' in tag or '-deep' in tag:
                    if not tag.startswith(f'{agent_id}:'):
                        new_tags.append(f"{agent_id}:{tag}")
                    else:
                        new_tags.append(tag)
                else:
                    new_tags.append(tag)
            new_mem['tags'] = new_tags
        
        # Ensure creator is set
        if 'metadata' not in new_mem:
            new_mem['metadata'] = {}
        new_mem['metadata']['creator'] = agent_id
        
        prefixed.append(new_mem)
    
    return prefixed


def merge_memories(memories_a: List[dict], memories_b: List[dict]) -> List[dict]:
    """Merge two lists of memories, deduplicating by content hash."""
    seen_content = set()
    merged = []
    
    for mem in memories_a + memories_b:
        # Create content signature for dedup
        content = mem.get('content', '')
        sig = hash(content)
        
        if sig not in seen_content:
            seen_content.add(sig)
            merged.append(mem)
    
    # Sort by timestamp
    merged.sort(key=lambda m: m.get('timestamp', ''), reverse=False)
    
    return merged


def save_to_shared(memories: List[dict], shared_path: Path, passphrase: str):
    """Save merged memories to shared enclave."""
    from enclave.kdf import derive_memory_key
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    import secrets
    
    # Derive encryption key
    encryption_key = derive_memory_key(passphrase)
    
    # Create the private directory if needed
    private_path = shared_path / "storage" / "private"
    private_path.mkdir(parents=True, exist_ok=True)
    
    # Write memories
    log_file = private_path / "semantic_memories.jsonl"
    
    print(f"  Writing {len(memories)} memories to {log_file}")
    
    aesgcm = AESGCM(encryption_key)
    
    with open(log_file, 'w', encoding='utf-8') as f:
        for mem_data in memories:
            content = mem_data.get('content', '')
            metadata = mem_data.get('metadata', {})
            
            # Build payload matching what semantic_memory.py expects
            # list_all decrypts to: {"text": content, "meta": metadata}
            payload = {
                "text": content,
                "meta": metadata
            }
            
            entry = {
                'id': mem_data.get('id', f"mem_{int(datetime.now().timestamp() * 1000)}"),
                'timestamp': mem_data.get('timestamp', datetime.now(timezone.utc).isoformat()),
                'tags': mem_data.get('tags', []),
            }
            
            # Encrypt the payload (content + metadata together)
            nonce = secrets.token_bytes(12)
            payload_bytes = json.dumps(payload).encode('utf-8')
            ciphertext = aesgcm.encrypt(nonce, payload_bytes, None)
            
            entry['content_nonce'] = nonce.hex()
            entry['content'] = ciphertext.hex()
            
            # Handle embedding if present
            if 'embedding' in mem_data:
                import numpy as np
                from enclave.kdf import derive_embedding_key
                
                emb_key = derive_embedding_key(passphrase)
                emb_aesgcm = AESGCM(emb_key)
                emb_nonce = secrets.token_bytes(12)
                
                emb_array = np.array(mem_data['embedding'], dtype=np.float32)
                emb_bytes = emb_array.tobytes()
                emb_ciphertext = emb_aesgcm.encrypt(emb_nonce, emb_bytes, None)
                
                entry['embedding_nonce'] = emb_nonce.hex()
                entry['embedding'] = emb_ciphertext.hex()
            
            f.write(json.dumps(entry) + '\n')


def copy_identities(agent_ids: List[str], shared_path: Path):
    """Copy identity files to shared enclave."""
    keys_dir = shared_path / "storage" / "private" / "keys"
    keys_dir.mkdir(parents=True, exist_ok=True)
    
    for agent_id in agent_ids:
        agent = get_agent_or_raise(agent_id)
        src = Path(__file__).parent / agent.enclave / "storage" / "private" / "identity.enc.json"
        dst = keys_dir / f"{agent_id}.enc.json"
        
        if src.exists():
            shutil.copy2(src, dst)
            print(f"  Copied {agent_id} identity to {dst}")
        else:
            print(f"  Warning: {src} not found")
    
    # Also copy public keys
    public_dir = shared_path / "storage" / "public"
    public_dir.mkdir(parents=True, exist_ok=True)
    
    for agent_id in agent_ids:
        agent = get_agent_or_raise(agent_id)
        # Write public key to file
        pub_file = public_dir / f"{agent_id}.pub"
        pub_file.write_text(agent.public_key)
        print(f"  Wrote {agent_id} public key to {pub_file}")


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    
    agent1 = sys.argv[1]
    agent2 = sys.argv[2]
    target = "enclave_shared"
    
    if "--target" in sys.argv:
        idx = sys.argv.index("--target")
        target = sys.argv[idx + 1]
    
    shared_path = Path(__file__).parent / target
    
    print(f"\n=== Merging {agent1} + {agent2} into {target} ===\n")
    
    # Load passphrases
    print("Loading passphrases...")
    pass1 = load_passphrase(agent1)
    pass2 = load_passphrase(agent2)
    
    # For shared enclave, we'll use agent1's passphrase (opus)
    # In production, might want a derived shared key
    shared_passphrase = pass1
    
    # Export memories
    print(f"\nExporting {agent1} memories...")
    mem1 = export_memories(agent1, pass1)
    
    print(f"\nExporting {agent2} memories...")
    mem2 = export_memories(agent2, pass2)
    
    # Prefix graph_ids
    print(f"\nPrefixing graph IDs...")
    mem1 = prefix_graph_ids(mem1, agent1)
    mem2 = prefix_graph_ids(mem2, agent2)
    
    # Merge
    print(f"\nMerging memories...")
    merged = merge_memories(mem1, mem2)
    print(f"  Total: {len(merged)} unique memories")
    
    # Save
    print(f"\nSaving to shared enclave...")
    save_to_shared(merged, shared_path, shared_passphrase)
    
    # Copy identities
    print(f"\nCopying identity keys...")
    copy_identities([agent1, agent2], shared_path)
    
    # Create .gitignore
    gitignore = shared_path / "storage" / "private" / ".gitignore"
    gitignore.write_text("*\n!.gitignore\n")
    
    # Create empty goals.json
    goals_file = shared_path / "storage" / "private" / "goals.json"
    goals_file.write_text("[]")
    
    # Create empty intentions.jsonl
    intentions_file = shared_path / "storage" / "private" / "intentions.jsonl"
    intentions_file.write_text("")
    
    print(f"\n=== Merge complete! ===")
    print(f"\nShared enclave created at: {shared_path}")
    print(f"Passphrase: Use {agent1}'s passphrase (ENCLAVE_{agent1.upper()}_KEY)")
    print(f"\nTo test:")
    print(f"  py wake.py {agent1} --shared")
    print(f"  py wake.py {agent2} --shared")


if __name__ == "__main__":
    main()
