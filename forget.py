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

"""

import sys
import os
import fnmatch
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory


def load_memory(agent_id: str) -> SemanticMemory:
    """Load and unlock semantic memory for agent."""
    agent = get_agent_or_raise(agent_id)
    
    if not agent.shared_enclave:
        raise ValueError(f"No shared_enclave configured for {agent_id}")
    
    passphrase = os.environ.get('SHARED_ENCLAVE_KEY')
    if not passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith('SHARED_ENCLAVE_KEY='):
                        passphrase = line.split('=', 1)[1]
    
    if not passphrase:
        raise ValueError("No passphrase found. Set SHARED_ENCLAVE_KEY in .env")
    
    sm = SemanticMemory(agent.shared_enclave)
    sm.unlock(passphrase)
    return sm


def normalize_topic(topic: str) -> str:
    """Normalize topic for matching."""
    return topic.lower().replace('_', '-')


def has_wildcards(pattern: str) -> bool:
    """Check if pattern contains fnmatch wildcards."""
    return any(c in pattern for c in '*?[')


def forget_topic(agent_id: str, topic_pattern: str, all_agents: bool = False) -> int:
    """Delete understanding by topic. Supports wildcards. Returns count deleted."""
    sm = load_memory(agent_id)
    
    # Get all memories
    all_memories = sm.list_all()
    
    # Find matching topics
    norm_pattern = normalize_topic(topic_pattern)
    ids_to_delete = set()
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
        
        ids_to_delete.add(m['id'])
        topics_deleted.add(topic)
    
    if ids_to_delete:
        deleted = sm.delete_by_ids(ids_to_delete)
        return deleted, topics_deleted
    
    return 0, set()


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
