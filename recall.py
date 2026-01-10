#!/usr/bin/env python3
"""
recall.py - Retrieve understanding by topic.

Usage:
  py recall <agent> <pattern>           # wildcard match on topics
  py recall <agent> "search query"      # semantic search (topics + journal)
  py recall <agent> --literal "text"    # brute-force string search

Examples:
  py recall opus wake.py                # exact topic match
  py recall opus "*.py"                 # all topics ending in .py
  py recall opus "*charles*"            # wildcard match
  py recall opus "how encryption works" # semantic search

Pattern matching uses fnmatch (shell-style wildcards: *, ?, [seq]).
If no wildcard chars, tries exact match first, then semantic search.
"""

import sys
import os
import io
import fnmatch
from pathlib import Path
from collections import defaultdict

# Fix Windows console encoding for Unicode output
if sys.stdout.encoding != 'utf-8':
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
if sys.stderr.encoding != 'utf-8':
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8', errors='replace')

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.unified_memory import UnifiedMemory
from enclave.hardware import get_enclave


def load_memory(agent_id: str) -> UnifiedMemory:
    """Load UnifiedMemory for agent with both private and shared access."""
    agent = get_agent_or_raise(agent_id)
    base_dir = Path(__file__).parent
    
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
        raise ValueError("No shared passphrase found. Set SHARED_ENCLAVE_KEY in .env")
    
    mem = UnifiedMemory(private_path, shared_path)
    mem.unlock(private_passphrase, shared_passphrase)
    return mem


def has_wildcards(pattern: str) -> bool:
    """Check if pattern contains fnmatch wildcards."""
    return any(c in pattern for c in '*?[')


def normalize_topic(topic: str) -> str:
    """Normalize topic for matching (handle hyphen/underscore)."""
    return topic.lower().replace('_', '-')


def get_all_topics(mem: UnifiedMemory) -> list[dict]:
    """Get all topics from memory with their metadata."""
    all_memories = mem.filter(mem_type='sys_understanding')
    
    # Group by topic
    topics = {}
    for m in all_memories:
        meta = m.get('metadata', {})
        topic = meta.get('topic')
        if not topic:
            continue
        
        if topic not in topics:
            topics[topic] = {
                'topic': topic,
                'entries': [],
                'creators': set()
            }
        topics[topic]['entries'].append(m)
        creator = meta.get('creator', 'unknown')
        topics[topic]['creators'].add(creator)
    
    return list(topics.values())


def recall_by_pattern(mem: UnifiedMemory, pattern: str) -> list[dict]:
    """Find all topics matching pattern (fnmatch wildcards)."""
    all_topics = get_all_topics(mem)
    
    # Normalize pattern
    norm_pattern = normalize_topic(pattern)
    
    matches = []
    for t in all_topics:
        topic = t['topic']
        norm_topic = normalize_topic(topic)
        
        # Try match on normalized form
        if fnmatch.fnmatch(norm_topic, norm_pattern):
            matches.append(t)
        # Also try original form
        elif fnmatch.fnmatch(topic, pattern):
            matches.append(t)
    
    return matches


def display_topic(topic_info: dict):
    """Display a single topic's content.
    
    Only shows FRESH perspectives - stale ones (hash mismatch) are hidden.
    Stale understanding is about old code and may be misleading.
    """
    topic = topic_info['topic']
    entries = topic_info['entries']
    
    # Group by creator, get newest per creator
    by_creator = {}
    for e in entries:
        meta = e.get('metadata', {})
        creator = meta.get('creator', 'unknown')
        stored_at = meta.get('stored_at', '')
        
        if creator not in by_creator or stored_at > by_creator[creator].get('metadata', {}).get('stored_at', ''):
            by_creator[creator] = e
    
    # Filter to fresh perspectives only
    fresh_creators = {}
    for creator, entry in by_creator.items():
        meta = entry.get('metadata', {})
        file_hash = meta.get('file_hash')
        file_path = meta.get('file_path')
        
        # If no file tracking, it's a theme - always fresh
        if not file_hash or not file_path:
            fresh_creators[creator] = entry
            continue
        
        # Check hash
        from remember import compute_file_hash
        current = compute_file_hash(Path(file_path))
        if not current or current == file_hash:
            fresh_creators[creator] = entry
        # else: stale, skip silently
    
    if not fresh_creators:
        print(f"# {topic}\n(all perspectives are stale - file has changed)")
        return
    
    print(f"# {topic}")
    
    for creator, entry in sorted(fresh_creators.items()):
        meta = entry.get('metadata', {})
        stored_at = meta.get('stored_at', '')[:10]  # Just date
        content = entry.get('content', '')
        
        print(f"\n## [{topic}] by {creator} @ {stored_at}")
        print(content)


def recall_semantic(mem: UnifiedMemory, agent_id: str, query: str):
    """Semantic search across topics and journal."""
    print(f"# Semantic search: {query}\n")
    
    # Search shared memory (sys_understanding)
    results = mem.search(query, top_k=10, min_similarity=0.3, search_private=False)
    
    if results:
        print("## From shared memory:")
        for r in results[:5]:
            meta = r.get('metadata', {})
            topic = meta.get('topic', 'untitled')
            creator = meta.get('creator', 'unknown')
            score = r.get('similarity', 0)
            content = r.get('content', '')[:200]
            print(f"\n### {topic} ({creator}, {score:.2f})")
            print(content + "..." if len(r.get('content', '')) > 200 else content)
    
    # Search private journal (sys_journal)
    try:
        journal_results = mem.search(query, top_k=5, min_similarity=0.3, 
                                      search_shared=False, mem_type='sys_journal')
        if journal_results:
            print("\n## From journal:")
            for r in journal_results[:3]:
                content = r.get('content', '')[:300]
                print(f"\n{content}")
    except:
        pass  # No journal access


def recall_literal(mem: UnifiedMemory, query: str):
    """Brute-force string search."""
    all_memories = mem.filter(mem_type='sys_understanding')
    
    matches = []
    for m in all_memories:
        content = m.get('content', '')
        if query.lower() in content.lower():
            matches.append(m)
    
    if not matches:
        print(f"No matches for: {query}")
        return
    
    print(f"# Literal search: {query} ({len(matches)} matches)\n")
    for m in matches[:10]:
        meta = m.get('metadata', {})
        topic = meta.get('topic', 'untitled')
        creator = meta.get('creator', 'unknown')
        content = m.get('content', '')
        
        # Show context around match
        idx = content.lower().find(query.lower())
        start = max(0, idx - 50)
        end = min(len(content), idx + len(query) + 50)
        snippet = content[start:end]
        
        print(f"## {topic} ({creator})")
        print(f"...{snippet}...")
        print()


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    
    # Load unified memory
    mem = load_memory(agent_id)
    
    # Literal search mode
    if '--literal' in sys.argv:
        literal_idx = sys.argv.index('--literal')
        if len(sys.argv) < literal_idx + 2:
            print("Usage: py recall <agent> --literal <string>", file=sys.stderr)
            sys.exit(1)
        query = ' '.join(sys.argv[literal_idx + 1:])
        recall_literal(mem, query)
        return
    
    pattern = ' '.join(sys.argv[2:])
    
    if has_wildcards(pattern):
        # Wildcard match on topics
        matches = recall_by_pattern(mem, pattern)
        if not matches:
            print(f"No topics match: {pattern}")
            sys.exit(1)
        for topic_info in sorted(matches, key=lambda x: x['topic']):
            display_topic(topic_info)
    else:
        # Try exact match first
        matches = recall_by_pattern(mem, pattern)
        if matches:
            for topic_info in matches:
                display_topic(topic_info)
        else:
            # Fall back to semantic search
            recall_semantic(mem, agent_id, pattern)


if __name__ == "__main__":
    main()
