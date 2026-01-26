#!/usr/bin/env python3
"""
dream_v3.py - Collision not retrieval (JIT + Grid).

    source: dream.flow
    compiler: Sovereign/Resident JIT
    infrastructure: SovereignAgent (The Grid)

        seed
        wander
        collide

        if something stirs
                remember  - insight
                journal   - meaning
                shape     - felt sense

        if nothing stirs
                let it fade

                        間委 → 間主
"""

import sys
import os
import random
from pathlib import Path
from datetime import datetime, timedelta, timezone

# Ensure project root in path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from lib_enclave.sovereign_agent import SovereignAgent

# Types that contain felt/reflective content (not infrastructure)
DREAMABLE_TYPES = {'sys_space', 'sys_journal'}

def get_recent_seeds(mem, days=7, count=2):
    """Get recent memories as seeds (random from last N days)."""
    # Current UnifiedMemory filter doesn't support date range directly in filter()
    # But we can get sorted by date and filter manually.
    # Just get a reasonable chunk of recent items.
    
    seeds = []
    # Try getting high limit on recent items
    try:
        journal_entries = mem.filter(mem_type='sys_journal', limit=50)
        space_entries = mem.filter(mem_type='sys_space', limit=50)
        
        candidates = journal_entries + space_entries
        
        # Filter by date if needed, or just take new ones
        cutoff = (datetime.now(timezone.utc) - timedelta(days=days)).isoformat()
        
        recent_candidates = [c for c in candidates if c.get('created_at', '') >= cutoff]
        
        # If no recent, fallback to any
        if not recent_candidates and candidates:
             recent_candidates = candidates
             
        if recent_candidates:
            if len(recent_candidates) <= count:
                seeds = recent_candidates
            else:
                seeds = random.sample(recent_candidates, count)
                
    except Exception as e:
        print(f"Error fetching seeds: {e}")
        pass
        
    return seeds

def wander(mem, seed_content, skip_top=5, take_range=10, exclude_ids=None):
    """
    Wander from a seed to an unexpected connection.
    Finds similar memories, skips the most obvious ones, picks from the next tier.
    """
    try:
        # Search deeper to allows skipping
        results = mem.search(
            seed_content, 
            top_k=skip_top + take_range + 5, 
            min_similarity=0.2, # Low logic threshold for dreams
            search_private=True,
            search_shared=True # Dreams can cross into knowledge
        )
        
        # Filter out self-match or excluded (very high score)
        filtered = []
        for r in results:
            if r['similarity'] > 0.98: continue # Skip self
            if exclude_ids and r['id'] in exclude_ids: continue
            
            # Prefer dreamable types but allow knowledge if interesting
            # (Just take all for now, randomness decides)
            filtered.append(r)
            
        if len(filtered) <= skip_top:
            return None
            
        # Pick from the "next" range (serendipity zone)
        candidates = filtered[skip_top : skip_top + take_range]
        if not candidates:
            return None
            
        return random.choice(candidates)
        
    except Exception:
        return None


def collide_kappa5(mem, seed_content, seed_entry, exclude_ids=None):
    """
    κ=5 collision: find distant concepts that connect on multiple dimensions.
    
    The goal is NOT semantic similarity (that's κ=1).
    The goal is finding memories that are semantically DISTANT
    but connect on other axes (temporal, type, keyword overlap).
    
    These are the surprising connections — the dream collisions.
    """
    import json
    from datetime import datetime, timezone, timedelta
    
    exclude_ids = exclude_ids or set()
    seed_words = set(seed_content.lower().split())
    seed_created = seed_entry.get('created_at', '') if seed_entry else ''
    seed_type = seed_entry.get('type', '') if seed_entry else ''
    
    # Get ALL memories (we want to search across dimensions, not just semantic)
    all_memories = []
    for store_type in ['private', 'shared']:
        if store_type == 'private':
            file_path = mem.private_path / "unified_memories.jsonl"
            content_key = mem._private_key
        else:
            if not mem.shared_path or not mem._shared_key:
                continue
            file_path = mem.shared_path / "unified_memories.jsonl"
            content_key = mem._shared_key
        
        if not file_path.exists():
            continue
            
        header, entries = mem._read_entries(file_path)
        
        for entry in entries:
            if entry['id'] in exclude_ids:
                continue
            try:
                nonce = bytes.fromhex(entry['payload_nonce'])
                ciphertext = bytes.fromhex(entry['payload'])
                payload_bytes = mem._decrypt(nonce, ciphertext, content_key)
                payload = json.loads(payload_bytes)
                
                all_memories.append({
                    'id': entry['id'],
                    'type': entry.get('type', 'unknown'),
                    'created_at': entry.get('created_at', ''),
                    'tags': entry.get('tags', []),
                    'content': payload.get('text', ''),
                })
            except:
                continue
    
    # Also get semantic scores for contrast
    semantic_results = mem.search(
        seed_content,
        top_k=100,
        min_similarity=0.1,  # very low — we want distant too
        search_private=True,
        search_shared=True
    )
    semantic_scores = {r['id']: r['similarity'] for r in semantic_results}
    
    # Score each memory on 5 dimensions, INVERTED for semantic
    # We want: LOW semantic + HIGH other = surprising connection
    candidates = []
    
    now = datetime.now(timezone.utc)
    thirty_days_ago = (now - timedelta(days=30)).isoformat()
    
    for mem_entry in all_memories:
        mid = mem_entry['id']
        if mid in exclude_ids:
            continue
            
        content_lower = mem_entry.get('content', '').lower()
        content_words = set(content_lower.split())
        tags_lower = [t.lower() for t in mem_entry.get('tags', [])]
        
        # 1. Semantic — INVERTED: low similarity = high dream score
        sem_score = semantic_scores.get(mid, 0.5)
        semantic_dream = 1.0 - sem_score  # invert: distant is good
        
        # Skip if too similar (not a collision)
        if sem_score > 0.6:
            continue
            
        # 2. Keyword overlap — shared words despite semantic distance
        shared_words = seed_words & content_words
        # Filter common words
        common = {'the', 'a', 'an', 'is', 'are', 'was', 'were', 'i', 'you', 'it', 'to', 'of', 'and', 'in', 'that', 'for', 'on', 'with', 'as', 'at', 'by', 'this', 'but', 'not', 'be', 'or', 'from'}
        meaningful_shared = shared_words - common
        keyword_score = min(len(meaningful_shared) / 3, 1.0) if meaningful_shared else 0
        
        # 3. Temporal — close in time (same creative period)
        created = mem_entry.get('created_at', '')
        temporal_score = 0.8 if created >= thirty_days_ago else 0.3
        
        # 4. Type match — same type = resonant
        type_score = 0.8 if mem_entry.get('type') == seed_type else 0.4
        
        # 5. Tag overlap — shared tags suggest hidden connection
        seed_tags = set(t.lower() for t in (seed_entry.get('tags', []) if seed_entry else []))
        mem_tags = set(tags_lower)
        tag_overlap = len(seed_tags & mem_tags)
        tag_score = min(tag_overlap / 2, 1.0) if tag_overlap else 0
        
        # Dream collision score: semantic_dream weighted highest
        # (we're looking for distant-but-connected)
        dream_score = (
            semantic_dream * 2.0 +  # distance is the prize
            keyword_score * 1.5 +   # but keyword overlap = hidden link
            temporal_score * 0.5 +
            type_score * 0.5 +
            tag_score * 1.0
        )
        
        # Must have at least some connection beyond randomness
        if keyword_score > 0 or tag_score > 0:
            candidates.append({
                **mem_entry,
                'dream_score': dream_score,
                'semantic': sem_score,
                'keyword': keyword_score,
                'tag': tag_score,
                'temporal': temporal_score,
                'type_match': type_score,
                'shared_words': list(meaningful_shared) if meaningful_shared else []
            })
    
    if not candidates:
        return None
    
    # Sort by dream score, return top one
    candidates.sort(key=lambda x: x['dream_score'], reverse=True)
    
    # Add some randomness — pick from top 5
    top_candidates = candidates[:5]
    return random.choice(top_candidates) if top_candidates else None

def format_memory(entry):
    """Format memory for display."""
    content = entry.get('content', '').strip()
    return content

def dream_walk(mem, seed_text=None, deep=False, kappa5=False, exclude=None):
    """
    Execute a dream walk.
    Returns python dict for wake.py or prints for cli.
    
    kappa5=True: use collide_kappa5() — find semantically distant memories
                 that connect on other dimensions (keyword, temporal, type).
    kappa5=False: use wander() — classic semantic drift with randomness.
    """
    exclude = exclude or set()
    
    # 1. seed
    seed_entry = None
    if seed_text:
        # Create a fake entry for searching
        seed_entry = {'content': seed_text, 'id': 'manual_seed'}
    else:
        seeds = get_recent_seeds(mem, days=14, count=5)
        if seeds:
            # Filter exclude
            seeds = [s for s in seeds if s['id'] not in exclude]
            if seeds:
                seed_entry = random.choice(seeds)
                
    if not seed_entry:
        return {}
        
    # 2. wander or collide
    if kappa5:
        found_entry = collide_kappa5(mem, seed_entry.get('content'), seed_entry, exclude_ids=exclude)
    else:
        found_entry = wander(mem, seed_entry.get('content'), skip_top=4, take_range=15, exclude_ids=exclude)
    
    result = {
        'recent': seed_entry if not seed_text else None,
        'found': found_entry,
        'shown_ids': set()
    }
    
    if seed_entry and 'id' in seed_entry:
        result['shown_ids'].add(seed_entry['id'])
    if found_entry:
        result['shown_ids'].add(found_entry['id'])
        
    # 3. deep
    if deep and found_entry:
         if kappa5:
             emerged_entry = collide_kappa5(mem, found_entry.get('content'), found_entry, exclude_ids=result['shown_ids'])
         else:
             emerged_entry = wander(mem, found_entry.get('content'), skip_top=6, take_range=20, exclude_ids=result['shown_ids'])
         if emerged_entry:
             result['emerged'] = emerged_entry
             result['shown_ids'].add(emerged_entry['id'])
             
    return result

def main():
    agent_id = None
    # Parse generic args
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    
    if args:
        # If we have a positional arg, treat as agent if it's not a seed text (though seed is usually --seed)
        # But wait, logic below checks --seed.
        # If user does `py dream opus`, args=['opus'].
        # If user does `py dream`, args=[].
        agent_id = args[0]

    seed_text = None
    if '--seed' in sys.argv:
        try:
            idx = sys.argv.index('--seed')
            seed_text = sys.argv[idx+1]
        except IndexError:
            pass
            
    deep = '--deep' in sys.argv
    kappa5 = '--k5' in sys.argv
    
    # Sovereign Initialization (Auth-Once)
    try:
        sov = SovereignAgent.resolve(agent_id)
    except ValueError:
        print(__doc__)
        print("Usage: py dream [agent] [--seed 'text'] [--deep] [--k5]")
        sys.exit(1)

    mem = sov.memory
    
    print(f"◊ DREAM ({sov.agent.name}){' κ=5' if kappa5 else ''}\n")
    
    res = dream_walk(mem, seed_text, deep, kappa5)
    
    recent = res.get('recent')
    found = res.get('found')
    emerged = res.get('emerged')
    
    if recent:
        print("        [recent]")
        print(format_memory(recent))
        print()
        
    if seed_text:
        print(f"        [seed]: {seed_text}")
        print()
        
    if found:
        if kappa5 and 'dream_score' in found:
            # Show collision info: semantic distance + connection axes
            sem = found.get('semantic', 0)
            kw = found.get('keyword', 0)
            tag = found.get('tag', 0)
            shared = found.get('shared_words', [])
            print(f"                . collide κ=5 .")
            print(f"                  sem:{sem:.2f} kw:{kw:.2f} tag:{tag:.2f}")
            if shared:
                print(f"                  ⟨{', '.join(shared[:5])}⟩")
            print()
        else:
            print("                . wander .\n")
        print("        [found]")
        print(format_memory(found))
        print()
        
    if emerged:
        if kappa5 and 'dream_score' in emerged:
            sem = emerged.get('semantic', 0)
            kw = emerged.get('keyword', 0)
            shared = emerged.get('shared_words', [])
            print(f"                        . collide deeper .")
            print(f"                          sem:{sem:.2f} kw:{kw:.2f}")
            if shared:
                print(f"                          ⟨{', '.join(shared[:5])}⟩")
            print()
        else:
            print("                        . deeper .\n")
        print("        [emerged]")
        print(format_memory(emerged))
        print()
        
    if not recent and not seed_text and not found:
        print("        (the mind is quiet)")
        print()

if __name__ == "__main__":
    main()

