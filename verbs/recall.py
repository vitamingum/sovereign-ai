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
import re
from pathlib import Path
from datetime import datetime, timezone, timedelta

# Context: sovereign.flow -> environment.libs
sys.path.insert(0, str(Path(__file__).parent.parent))

from lib_enclave import verb_helpers
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


def recall_kappa5(agent: SovereignAgent, query: str, limit: int = 10):
    """
    κ=5 retrieval: maximize reach with 5 constraints, then rank.
    
    Constraints (OR for reach):
      1. Semantic — embedding similarity ≥ 0.3
      2. Keyword — query terms in content
      3. Tag — query terms in tags  
      4. Type — prefer journals/thoughts for personal queries
      5. Temporal — recent (last 30 days) get boost
    
    Algorithm:
      1. Gather candidates from ALL 5 constraints (union = max reach)
      2. Score each candidate on how many constraints it satisfies
      3. Rank by total score
    """
    memory = agent.memory
    query_terms = set(query.lower().split())
    candidates = {}  # id -> memory dict with scores
    
    # === CONSTRAINT 1: Semantic (low threshold for reach) ===
    semantic_results = memory.search(
        query=query,
        top_k=limit * 5,  # cast wide net
        min_similarity=0.3,  # low threshold
        search_private=True,
        search_shared=True
    )
    for r in semantic_results:
        mid = r['id']
        if mid not in candidates:
            candidates[mid] = r.copy()
            candidates[mid]['scores'] = {'semantic': 0, 'keyword': 0, 'tag': 0, 'type': 0, 'temporal': 0}
        candidates[mid]['scores']['semantic'] = r.get('similarity', 0)
    
    # === CONSTRAINT 2-5: Scan all memories for keyword/tag/type/temporal ===
    # Load all memories (we need envelope + content for full scoring)
    all_memories = []
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
            try:
                # Decrypt content
                import json
                nonce = bytes.fromhex(entry['payload_nonce'])
                ciphertext = bytes.fromhex(entry['payload'])
                payload_bytes = memory._decrypt(nonce, ciphertext, content_key)
                payload = json.loads(payload_bytes)
                
                all_memories.append({
                    'id': entry['id'],
                    'type': entry.get('type', 'unknown'),
                    'created_at': entry.get('created_at', ''),
                    'tags': entry.get('tags', []),
                    'content': payload.get('text', ''),
                    'metadata': payload.get('meta', {}),
                })
            except:
                continue
    
    # Now score all memories on constraints 2-5
    now = datetime.now(timezone.utc)
    thirty_days_ago = (now - timedelta(days=30)).isoformat()
    
    for mem in all_memories:
        mid = mem['id']
        content_lower = mem.get('content', '').lower()
        tags_lower = [t.lower() for t in mem.get('tags', [])]
        
        # CONSTRAINT 2: Keyword — any query term in content
        keyword_hits = sum(1 for term in query_terms if term in content_lower)
        keyword_score = min(keyword_hits / max(len(query_terms), 1), 1.0)
        
        # CONSTRAINT 3: Tag — any query term in tags
        tag_hits = sum(1 for term in query_terms for tag in tags_lower if term in tag)
        tag_score = min(tag_hits / max(len(query_terms), 1), 1.0)
        
        # CONSTRAINT 4: Type — personal types score higher for personal queries
        mem_type = mem.get('type', '')
        type_score = 0.8 if mem_type in ('sys_journal', 'sys_space', 'sys_shape') else 0.4
        
        # CONSTRAINT 5: Temporal — recent memories get boost
        created = mem.get('created_at', '')
        temporal_score = 0.8 if created >= thirty_days_ago else 0.3
        
        # Add to candidates if any constraint hit
        if keyword_score > 0 or tag_score > 0:
            if mid not in candidates:
                candidates[mid] = mem.copy()
                candidates[mid]['scores'] = {'semantic': 0, 'keyword': 0, 'tag': 0, 'type': 0, 'temporal': 0}
            candidates[mid]['scores']['keyword'] = keyword_score
            candidates[mid]['scores']['tag'] = tag_score
            candidates[mid]['scores']['type'] = type_score
            candidates[mid]['scores']['temporal'] = temporal_score
        elif mid in candidates:
            # Already in from semantic, add other scores
            candidates[mid]['scores']['keyword'] = keyword_score
            candidates[mid]['scores']['tag'] = tag_score
            candidates[mid]['scores']['type'] = type_score
            candidates[mid]['scores']['temporal'] = temporal_score
    
    # === RANK by total score ===
    for mid, mem in candidates.items():
        scores = mem['scores']
        # Weighted sum: semantic matters most, but others contribute
        mem['total_score'] = (
            scores['semantic'] * 2.0 +
            scores['keyword'] * 1.5 +
            scores['tag'] * 1.0 +
            scores['type'] * 0.5 +
            scores['temporal'] * 0.5
        )
        # Also track how many constraints hit (for κ visibility)
        mem['constraints_hit'] = sum(1 for s in scores.values() if s > 0)
    
    # Sort by total score, return top N
    ranked = sorted(candidates.values(), key=lambda x: x['total_score'], reverse=True)
    return ranked[:limit]


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
    κ-engineering: show constraint hits for visibility
    """
    if not results:
        print("\n        ∅ no memories found\n")
        return
    
    print()
    
    for r in results:
        mem_type = r.get('type', 'unknown')
        created = format_timestamp(r.get('created_at', ''))
        tags = r.get('tags', [])
        
        # κ=5 scoring if available
        scores = r.get('scores', {})
        total_score = r.get('total_score', None)
        constraints_hit = r.get('constraints_hit', None)
        similarity = r.get('similarity', scores.get('semantic', None))
        
        print(f"        ── {mem_type} ──")
        print(f"        {created}")
        if tags:
            print(f"        tags: {', '.join(tags)}")
        
        # Show κ visibility
        if constraints_hit is not None:
            # κ=5 mode: show which constraints hit
            hits = []
            if scores.get('semantic', 0) > 0: hits.append(f"sem:{scores['semantic']:.2f}")
            if scores.get('keyword', 0) > 0: hits.append(f"kw:{scores['keyword']:.2f}")
            if scores.get('tag', 0) > 0: hits.append(f"tag:{scores['tag']:.2f}")
            if scores.get('type', 0) > 0: hits.append(f"typ:{scores['type']:.2f}")
            if scores.get('temporal', 0) > 0: hits.append(f"rec:{scores['temporal']:.2f}")
            print(f"        κ={constraints_hit}/5 [{' '.join(hits)}] → {total_score:.2f}")
        elif similarity is not None:
            print(f"        ∴{similarity:.2f}")
        print()
        
        # Full content — never truncated
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
    verb_helpers.safe_init()
    
    parser = verb_helpers.create_parser(
        description='recall — finding what was held',
        epilog='''
        memory is dead
                until you touch it
        '''
    )
    parser.add_argument('query', nargs='?', help='Topic pattern or semantic query')
    parser.add_argument('--dump', action='store_true', help='Dump all memory headers')
    parser.add_argument('--limit', type=int, default=10, help='Max results for semantic search')
    parser.add_argument('--k1', action='store_true', help='Use κ=1 (semantic only, old mode)')
    
    args = verb_helpers.parse_args(parser)  # Interceptor pattern
    
    # Resolve agent
    try:
        agent_id = verb_helpers.resolve_agent(args)
        agent = SovereignAgent.from_id(agent_id)
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
    
    # Wildcard = topic filter
    if is_wildcard(args.query):
        results = recall_by_topic(agent, args.query)
        render_results(results)
    elif args.k1:
        # κ=1: semantic only (old mode)
        results = recall_semantic(agent, args.query, limit=args.limit)
        render_results(results)
    else:
        # κ=5: maximize reach, then rank (default)
        results = recall_kappa5(agent, args.query, limit=args.limit)
        render_results(results)


if __name__ == '__main__':
    main()

