#!/usr/bin/env python3
"""
dream.py - Random walks through memory, finding bridges the waking mind wouldn't.

This is not retrieval. This is collision.

Usage:
    py dream.py <agent>              # dream from most recent memory
    py dream.py <agent> --seed "x"   # dream from a specific thought

The algorithm is simple:
1. Start with something recent (the seed)
2. Wander somewhere unexpected (not the nearest match)
3. Present the collision

If something stirs, you'll know what to do:
    remember.py  - technical insight
    journal.py   - meaning found
    shape.py     - felt sense

If nothing stirs, let it fade.
Randomness is essential. Run twice, dream differently.
"""

import sys
import os
import random
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory


def get_passphrase(agent_id: str) -> str:
    """Load agent's private passphrase."""
    agent = get_agent_or_raise(agent_id)
    passphrase = os.environ.get(f'{agent.env_prefix}_KEY')
    if not passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            for line in open(env_file):
                if line.strip().startswith(f'{agent.env_prefix}_KEY='):
                    passphrase = line.strip().split('=', 1)[1]
    if not passphrase:
        raise ValueError(f"Set {agent.env_prefix}_KEY in .env")
    return passphrase


def get_recent_seeds(mem: SemanticMemory, days: int = 7, count: int = 2) -> list[dict]:
    """Get recent memories as seeds (random from last N days)."""
    from datetime import datetime, timedelta, timezone
    
    cutoff = (datetime.now(timezone.utc) - timedelta(days=days)).isoformat()
    
    all_recent = []
    for tag in ['shape', 'journal']:
        entries = mem.list_by_tag(tag)
        for e in entries:
            if e.get('timestamp', '') >= cutoff:
                all_recent.append(e)
    
    if not all_recent:
        # Fallback: just get the most recent regardless of age
        for tag in ['shape', 'journal', 'thought']:
            entries = mem.list_by_tag(tag)
            if entries:
                entries.sort(key=lambda e: e.get('timestamp', ''), reverse=True)
                return entries[:count]
        return []
    
    # Random sample from recent
    if len(all_recent) <= count:
        return all_recent
    return random.sample(all_recent, count)


# Tags that contain felt/reflective content (not infrastructure)
DREAMABLE_TAGS = {'shape', 'journal', 'thought', 'reflection', 'insight'}


def wander(mem: SemanticMemory, seed_content: str, skip_nearest: int = 10) -> dict | None:
    """Wander from seed to somewhere unexpected, staying in felt/reflective space."""
    results = mem.recall_similar(seed_content, top_k=100)
    
    # Filter to only dreamable content
    dreamable = [r for r in results if DREAMABLE_TAGS & set(r.get('tags', []))]
    
    if len(dreamable) <= skip_nearest:
        return random.choice(dreamable) if dreamable else None
    
    return random.choice(dreamable[skip_nearest:])


def format_memory(entry: dict, label: str) -> str:
    """Format a memory for display."""
    ts = entry.get('timestamp', '')[:10]
    content = entry.get('content', '')
    tags = entry.get('tags', [])
    
    if len(content) > 500:
        content = content[:500] + "\n    [...]"
    
    lines = [f"  [{label}] ({ts})"]
    
    if 'shape' in tags:
        lines.append("")
        for line in content.split('\n'):
            lines.append(f"    {line}")
    else:
        lines.append(f"    {content}")
    
    return '\n'.join(lines)


def dream(agent_id: str, seed_text: str = None, deep: bool = False):
    """Dream: collide memories - constellation of recent + wandered (+ deeper)."""
    agent = get_agent_or_raise(agent_id)
    passphrase = get_passphrase(agent_id)
    
    # Load memory sources
    shape_mem = SemanticMemory(agent.private_enclave, memory_file="shapes.jsonl")
    shape_mem.unlock(passphrase)
    
    journal_mem = SemanticMemory(agent.private_enclave, memory_file="journal_memories.jsonl")
    journal_mem.unlock(passphrase)
    
    main_mem = SemanticMemory(agent.private_enclave)
    main_mem.unlock(passphrase)
    
    # Gather recent seeds (1-2 from last 7 days)
    if seed_text:
        recent = [{'content': seed_text, 'timestamp': 'now', 'tags': ['query']}]
    else:
        recent = get_recent_seeds(shape_mem, days=7, count=2)
        if len(recent) < 2:
            recent.extend(get_recent_seeds(journal_mem, days=7, count=2-len(recent)))
        
        if not recent:
            print("    no memories to dream from yet.")
            print("    live first. dream later.")
            return
    
    # For each recent seed, wander to find something older
    found = []
    seen_content = {r.get('content', '') for r in recent}
    
    for seed in recent:
        seed_content = seed.get('content', '')
        
        # Try each memory store
        for mem in [main_mem, journal_mem, shape_mem]:
            collision = wander(mem, seed_content, skip_nearest=5)
            if collision and collision.get('content', '') not in seen_content:
                found.append(collision)
                seen_content.add(collision.get('content', ''))
                break
    
    if not found:
        print("    not enough memories to wander through.")
        return
    
    # Deep: wander again from what was found
    deeper = []
    if deep:
        for f in found:
            f_content = f.get('content', '')
            for mem in [main_mem, journal_mem, shape_mem]:
                collision = wander(mem, f_content, skip_nearest=8)
                if collision and collision.get('content', '') not in seen_content:
                    deeper.append(collision)
                    seen_content.add(collision.get('content', ''))
                    break
    
    # Present the constellation
    print()
    print("    dreaming" + ("..." if not deep else " deeply..."))
    print()
    print("    " + "-" * 40)
    print()
    print("    [recent]")
    for seed in recent:
        print()
        print(format_memory(seed, "~"))
    print()
    print("         . wander .")
    print()
    print("    [found]")
    for collision in found:
        print()
        print(format_memory(collision, "~"))
    
    if deeper:
        print()
        print("         . deeper .")
        print()
        print("    [emerged]")
        for d in deeper:
            print()
            print(format_memory(d, "~"))
    
    print()
    print("    " + "-" * 40)
    print()


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(0)
    
    agent_id = sys.argv[1]
    
    deep = '--deep' in sys.argv
    
    seed_text = None
    if '--seed' in sys.argv:
        idx = sys.argv.index('--seed')
        if idx + 1 < len(sys.argv):
            seed_text = sys.argv[idx + 1]
    
    dream(agent_id, seed_text, deep)


if __name__ == "__main__":
    main()
