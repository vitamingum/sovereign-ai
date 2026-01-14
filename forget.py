#!/usr/bin/env python3
"""
forget.py - Delete understanding by topic.

Usage:
    py forget <agent> <topic>           # Delete your understanding of topic
    py forget <agent> <topic> --all     # Delete ALL agents' understanding

Examples:
    py forget opus wake.py
    py forget opus old-concept
    py forget opus "*.py" --all         # Wildcard supported

                        間委 → 間主
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enclave_shared.unicode_fix import fix_streams  # 間

import fnmatch
from pathlib import Path

from enclave_shared.config import get_agent_or_raise
from enclave_shared.unified_memory import UnifiedMemory
from enclave_shared.hardware import get_enclave


def load_memory(agent_id: str) -> UnifiedMemory:
    """Load and unlock unified memory for agent (shared enclave)."""
    agent = get_agent_or_raise(agent_id)
    base_dir = Path(__file__).parent
    
    if not agent.shared_enclave:
        raise ValueError(f"No shared_enclave configured for {agent_id}")
    
    private_path = base_dir / agent.private_enclave / "storage" / "private"
    shared_path = base_dir / agent.shared_enclave / "storage" / "encrypted"
    
    # Get private passphrase
    private_passphrase = None
    key_file = private_path / "key.sealed"
    if key_file.exists():
        try:
            with open(key_file, "rb") as f:
                sealed_data = f.read()
            enclave = get_enclave()
            private_passphrase = enclave.unseal(sealed_data).decode('utf-8')
        except Exception:
            pass
    
    if not private_passphrase:
        private_passphrase = os.environ.get(f'{agent.env_prefix}_KEY')
    
    if not private_passphrase:
        env_file = base_dir / '.env'
        if env_file.exists():
            for line in env_file.read_text().splitlines():
                if line.startswith(f'{agent.env_prefix}_KEY='):
                    private_passphrase = line.split('=', 1)[1]
    
    if not private_passphrase:
        raise ValueError(f"No passphrase found for {agent_id}")
    
    # Get shared passphrase
    shared_passphrase = os.environ.get('SHARED_ENCLAVE_KEY')
    if not shared_passphrase:
        env_file = base_dir / '.env'
        if env_file.exists():
            for line in env_file.read_text().splitlines():
                if line.startswith('SHARED_ENCLAVE_KEY='):
                    shared_passphrase = line.split('=', 1)[1]
    
    if not shared_passphrase:
        raise ValueError("No passphrase found. Set SHARED_ENCLAVE_KEY in .env")
    
    mem = UnifiedMemory(private_path, shared_path)
    mem.unlock(private_passphrase, shared_passphrase)
    return mem


def normalize_topic(topic: str) -> str:
    """Normalize topic for matching."""
    return topic.lower().replace('_', '-')


def has_wildcards(pattern: str) -> bool:
    """Check if pattern contains fnmatch wildcards."""
    return any(c in pattern for c in '*?[')


def forget_topic(agent_id: str, topic_pattern: str, all_agents: bool = False) -> int:
    """Delete understanding by topic. Supports wildcards. Returns count deleted."""
    mem = load_memory(agent_id)
    
    # Get all understanding entries
    all_memories = mem.filter(mem_type='sys_understanding')
    
    # Find matching topics
    norm_pattern = normalize_topic(topic_pattern)
    ids_to_delete = []
    topics_deleted = set()
    
    for m in all_memories:
        meta = m.get('metadata', {})
        topic = meta.get('topic', '')
        creator = meta.get('creator', '')
        
        if not topic:
            continue
        
        # Check match
        norm_topic = normalize_topic(topic)
        matches = fnmatch.fnmatch(norm_topic, norm_pattern) or fnmatch.fnmatch(topic, topic_pattern)
        
        if not matches:
            continue
        
        # Check creator filter
        if not all_agents and creator != agent_id:
            continue
        
        ids_to_delete.append(m['id'])
        topics_deleted.add(topic)
    
    # Delete each matching entry
    deleted_count = 0
    for mem_id in ids_to_delete:
        if mem.delete(mem_id):
            deleted_count += 1
    
    return deleted_count, topics_deleted


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    topic = sys.argv[2]
    all_agents = '--all' in sys.argv
    
    try:
        deleted, topics = forget_topic(agent_id, topic, all_agents)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    
    if deleted:
        scope = "all agents" if all_agents else agent_id
        if len(topics) == 1:
            print(f"✅ Forgot: {list(topics)[0]} ({deleted} entries, {scope})")
        else:
            print(f"✅ Forgot {len(topics)} topics ({deleted} entries, {scope})")
            for t in sorted(topics):
                print(f"  - {t}")
    else:
        print(f"Nothing to forget: {topic}")


if __name__ == "__main__":
    main()
