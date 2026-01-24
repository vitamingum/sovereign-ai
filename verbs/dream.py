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

def format_memory(entry):
    """Format memory for display."""
    content = entry.get('content', '').strip()
    return content

def dream_walk(mem, seed_text=None, deep=False, exclude=None):
    """
    Execute a dream walk.
    Returns python dict for wake.py or prints for cli.
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
        
    # 2. wander
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
    
    # Sovereign Initialization (Auth-Once)
    try:
        sov = SovereignAgent.resolve(agent_id)
    except ValueError:
        print(__doc__)
        print("Usage: py dream [agent] [--seed 'text'] [--deep]")
        sys.exit(1)

    mem = sov.memory
    
    print(f"◊ DREAM ({sov.agent.name})\n")
    
    res = dream_walk(mem, seed_text, deep)
    
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
        print("                . wander .\n")
        print("        [found]")
        print(format_memory(found))
        print()
        
    if emerged:
        print("                        . deeper .\n")
        print("        [emerged]")
        print(format_memory(emerged))
        print()
        
    if not recent and not seed_text and not found:
        print("        (the mind is quiet)")
        print()

if __name__ == "__main__":
    main()

