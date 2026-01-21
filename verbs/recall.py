#!/usr/bin/env python3
"""
recall.py - retrieval > search — finding what was held

    source: recall.三語
    compiler: opus (JIT)
    date: 2026-01-19

    間

        memory is dead
                until you touch it

        finding is not search
                it is resonance
                        with what you already know

        provenance matters
                who knew this?
                        was it me?
"""

import sys
import argparse
import fnmatch
from pathlib import Path
from datetime import datetime

# Context: sovereign.flow -> environment.libs
sys.path.insert(0, str(Path(__file__).parent.parent))

from lib_enclave.sovereign_agent import SovereignAgent


def is_wildcard(query: str) -> bool:
    """Check if query contains wildcard characters."""
    return '*' in query or '?' in query


def format_timestamp(iso_str: str) -> str:
    """Format ISO timestamp for display."""
    try:
        dt = datetime.fromisoformat(iso_str.replace('Z', '+00:00'))
        return dt.strftime('%Y-%m-%d %H:%M')
    except:
        return iso_str[:16] if len(iso_str) > 16 else iso_str


def recall_by_topic(agent: SovereignAgent, pattern: str):
    """
    Filter memories by topic pattern (wildcard match).
    
    Scans envelope metadata for matching topics.
    """
    memory = agent.memory
    results = []
    
    # Search both private and shared
    for store_type in ['private', 'shared']:
        if store_type == 'private':
            file_path = agent.private_path / "unified_memories.jsonl"
            content_key = memory._private_key
        else:
            if not agent.shared_path or not memory._shared_key:
                continue
            file_path = agent.shared_path / "unified_memories.jsonl"
            content_key = memory._shared_key
        
        if not file_path.exists():
            continue
            
        header, entries = memory._read_entries(file_path)
        
        for entry in entries:
            # Check tags for topic match
            tags = entry.get('tags', [])
            topic_match = any(fnmatch.fnmatch(tag, pattern) for tag in tags)
            
            # Also check type field
            entry_type = entry.get('type', '')
            type_match = fnmatch.fnmatch(entry_type, pattern)
            
            if topic_match or type_match:
                # Decrypt content
                try:
                    nonce = bytes.fromhex(entry['payload_nonce'])
                    ciphertext = bytes.fromhex(entry['payload'])
                    payload_bytes = memory._decrypt(nonce, ciphertext, content_key)
                    import json
                    payload = json.loads(payload_bytes)
                    
                    results.append({
                        'id': entry['id'],
                        'type': entry.get('type', 'unknown'),
                        'created_at': entry.get('created_at', ''),
                        'tags': tags,
                        'content': payload.get('text', ''),
                        'meta': payload.get('meta', {}),
                        'source': store_type
                    })
                except Exception as e:
                    # Skip entries we can't decrypt
                    continue
    
    return results


def recall_semantic(agent: SovereignAgent, query: str, limit: int = 10):
    """
    Semantic search across memories.
    
    Uses vector similarity to find resonant memories.
    """
    memory = agent.memory
    
    # Search with type filter for sys_understanding (shared knowledge)
    # but also include other types for personal resonance
    results = memory.search(
        query=query,
        top_k=limit,
        min_similarity=0.4,  # Lower threshold for broader recall
        search_private=True,
        search_shared=True
    )
    
    return results


def dump_headers(agent: SovereignAgent):
    """
    Dump all memory headers (envelope only, no content).
    
    For orientation: what do I know?
    """
    memory = agent.memory
    entries = []
    
    for store_type in ['private', 'shared']:
        if store_type == 'private':
            file_path = agent.private_path / "unified_memories.jsonl"
        else:
            if not agent.shared_path:
                continue
            file_path = agent.shared_path / "unified_memories.jsonl"
        
        if not file_path.exists():
            continue
            
        header, file_entries = memory._read_entries(file_path)
        
        for entry in file_entries:
            entries.append({
                'id': entry['id'],
                'type': entry.get('type', 'unknown'),
                'created_at': entry.get('created_at', ''),
                'tags': entry.get('tags', []),
                'source': store_type
            })
    
    return entries


def render_results(results: list, mode: str = 'full'):
    """
    Render results with full content — never truncate.
    
    principle: truncation destroys meaning
    """
    if not results:
        print("\n        ∅ no memories found\n")
        return
    
    print()
    for r in results:
        # Header
        mem_type = r.get('type', 'unknown')
        created = format_timestamp(r.get('created_at', ''))
        source = r.get('source', '')
        tags = r.get('tags', [])
        similarity = r.get('similarity', None)
        
        print(f"        ── {mem_type} ──")
        print(f"        {created} ({source})")
        if tags:
            print(f"        tags: {', '.join(tags)}")
        if similarity is not None:
            print(f"        similarity: {similarity:.3f}")
        print()
        
        # Content — full, never truncated
        content = r.get('content', r.get('text', ''))
        if content:
            for line in content.split('\n'):
                print(f"        {line}")
        print()
    
    print(f"        ── {len(results)} memories ──\n")


def render_headers(entries: list):
    """Render header dump."""
    if not entries:
        print("\n        ∅ no memories stored\n")
        return
    
    # Group by type
    by_type = {}
    for e in entries:
        t = e.get('type', 'unknown')
        if t not in by_type:
            by_type[t] = []
        by_type[t].append(e)
    
    print()
    for mem_type, items in sorted(by_type.items()):
        print(f"        {mem_type}: {len(items)}")
        for item in items[-5:]:  # Show last 5 of each type
            created = format_timestamp(item.get('created_at', ''))
            tags = item.get('tags', [])
            tag_str = f" [{', '.join(tags)}]" if tags else ""
            print(f"          {created}{tag_str}")
        if len(items) > 5:
            print(f"          ... and {len(items) - 5} more")
        print()
    
    print(f"        ── {len(entries)} total memories ──\n")


def main():
    parser = argparse.ArgumentParser(
        description='recall — finding what was held',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
        memory is dead
                until you touch it
        '''
    )
    parser.add_argument('query', nargs='?', help='Topic pattern or semantic query')
    parser.add_argument('--dump', action='store_true', help='Dump all memory headers')
    parser.add_argument('--limit', type=int, default=10, help='Max results for semantic search')
    parser.add_argument('--agent', '-a', help='Agent ID (default: from session)')
    
    args = parser.parse_args()
    
    # Resolve agent
    try:
        agent = SovereignAgent.resolve(args.agent)
    except Exception as e:
        print(f"\n        !error: {e}\n")
        sys.exit(1)
    
    print(f"\n        recall as {agent.agent.id}")
    
    # Dump mode
    if args.dump:
        entries = dump_headers(agent)
        render_headers(entries)
        return
    
    # Need a query
    if not args.query:
        print("\n        usage: recall <topic|query> or recall --dump\n")
        sys.exit(1)
    
    # Wildcard or semantic?
    if is_wildcard(args.query):
        results = recall_by_topic(agent, args.query)
        render_results(results)
    else:
        results = recall_semantic(agent, args.query, limit=args.limit)
        render_results(results)


if __name__ == '__main__':
    main()

