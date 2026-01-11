#!/usr/bin/env python3
"""
dream.py - collision not retrieval

Usage:
    py dream.py <agent>              # from most recent
    py dream.py <agent> --seed "x"   # from specific thought
    py dream.py <agent> --deep       # wander twice

        seed
        wander
        collide

        if something stirs
                remember  - insight
                journal   - meaning
                shape     - felt sense

        if nothing stirs
                let it fade

        run twice
                dream differently
"""

import sys
import os
import io
import random
from pathlib import Path
from datetime import datetime, timedelta, timezone

# Fix Windows console encoding for Unicode output
if sys.stdout.encoding != 'utf-8':
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
if sys.stderr.encoding != 'utf-8':
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8', errors='replace')

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enclave_shared.config import get_agent_or_raise
from enclave_shared.unified_memory import UnifiedMemory
from enclave_shared.hardware import get_enclave


# Types that contain felt/reflective content (not infrastructure)
DREAMABLE_TYPES = {'sys_space', 'sys_journal'}


def load_memory(agent_id: str) -> UnifiedMemory:
    """Load UnifiedMemory for an agent."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
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
        private_passphrase = os.environ.get(f'{prefix}_KEY')
    
    if not private_passphrase:
        env_file = base_dir / '.env'
        if env_file.exists():
            for line in env_file.read_text().splitlines():
                if line.startswith(f'{prefix}_KEY='):
                    private_passphrase = line.split('=', 1)[1]
    
    if not private_passphrase:
        raise ValueError(f"Set {prefix}_KEY in .env")
    
    # Get shared passphrase
    shared_passphrase = os.environ.get('SHARED_ENCLAVE_KEY')
    if not shared_passphrase:
        env_file = base_dir / '.env'
        if env_file.exists():
            for line in env_file.read_text().splitlines():
                if line.startswith('SHARED_ENCLAVE_KEY='):
                    shared_passphrase = line.split('=', 1)[1]
    
    mem = UnifiedMemory(private_path, shared_path)
    mem.unlock(private_passphrase, shared_passphrase)
    return mem


def get_recent_seeds(mem: UnifiedMemory, days: int = 7, count: int = 2) -> list[dict]:
    """Get recent memories as seeds (random from last N days)."""
    cutoff = (datetime.now(timezone.utc) - timedelta(days=days)).isoformat()
    
    all_recent = []
    for mem_type in DREAMABLE_TYPES:
        entries = mem.filter(mem_type=mem_type)
        for e in entries:
            if e.get('created_at', '') >= cutoff:
                all_recent.append(e)
    
    if not all_recent:
        # Fallback: just get the most recent regardless of age
        for mem_type in DREAMABLE_TYPES:
            entries = mem.filter(mem_type=mem_type, limit=count)
            if entries:
                return entries[:count]
        return []
    
    # Random sample from recent
    if len(all_recent) <= count:
        return all_recent
    return random.sample(all_recent, count)


def wander(mem: UnifiedMemory, seed_content: str, exclude: set[str], skip_nearest: int = 5) -> dict | None:
    """Wander from seed to somewhere unexpected, staying in dreamable space."""
    # Search with higher top_k to have options
    results = mem.search(seed_content, top_k=50, min_similarity=0.3)
    
    # Filter to only dreamable content and not excluded
    dreamable = [
        r for r in results 
        if r.get('type') in DREAMABLE_TYPES and r.get('id') not in exclude
    ]
    
    if not dreamable:
        return None
    
    if len(dreamable) <= skip_nearest:
        return random.choice(dreamable)
    
    # Skip the nearest matches, pick randomly from the rest
    return random.choice(dreamable[skip_nearest:])


def format_memory(entry: dict, label: str = None) -> str:
    """Format a memory for display."""
    ts = entry.get('created_at', '')[:10]
    content = entry.get('content', '')
    mem_type = entry.get('type', '')
    
    lines = []
    if label:
        lines.append(f"[{label}]")
    lines.append(f"[{ts}]")
    lines.append("")
    
    # sys_space entries have indented formatting (storage uses sys_shape)
    if mem_type in ('sys_space', 'sys_shape'):
        for line in content.split('\n'):
            lines.append(f"    {line}")
    else:
        lines.append(content)
    
    return '\n'.join(lines)


def dream_walk(mem: UnifiedMemory, seed_text: str = None, deep: bool = False, exclude: set[str] = None) -> dict:
    """
    Dream walk - for wake.py to call.
    
    Returns {recent, found, deeper, shown_ids}
    """
    exclude = exclude or set()
    shown_ids = set()
    
    # Get seed
    if seed_text:
        recent = [{'id': 'query', 'content': seed_text, 'created_at': 'now', 'type': 'query'}]
    else:
        recent = get_recent_seeds(mem, days=7, count=1)
        if not recent:
            return {'recent': None, 'found': None, 'deeper': None, 'shown_ids': set()}
    
    seed = recent[0]
    shown_ids.add(seed.get('id', ''))
    
    # Wander from seed
    seed_content = seed.get('content', '')
    found = wander(mem, seed_content, exclude | shown_ids, skip_nearest=5)
    
    if found:
        shown_ids.add(found.get('id', ''))
    
    # Deep: wander again from what was found
    deeper = None
    if deep and found:
        found_content = found.get('content', '')
        deeper = wander(mem, found_content, exclude | shown_ids, skip_nearest=8)
        if deeper:
            shown_ids.add(deeper.get('id', ''))
    
    return {
        'recent': seed,
        'found': found,
        'deeper': deeper,
        'shown_ids': shown_ids
    }


def dream(agent_id: str, seed_text: str = None, deep: bool = False):
    """Dream: collide memories - constellation of recent + wandered (+ deeper)."""
    mem = load_memory(agent_id)
    
    result = dream_walk(mem, seed_text, deep)
    
    if not result['recent']:
        print("    no memories to dream from yet.")
        print("    live first. dream later.")
        return
    
    if not result['found']:
        print("    not enough memories to wander through.")
        return
    
    # Present the constellation
    print()
    print("    dreaming" + ("..." if not deep else " deeply..."))
    print()
    print("    " + "-" * 40)
    print()
    print("[recent]")
    print(format_memory(result['recent']))
    print()
    print("     . wander .")
    print()
    print("[found]")
    print(format_memory(result['found']))
    
    if result['deeper']:
        print()
        print("     . deeper .")
        print()
        print("[emerged]")
        print(format_memory(result['deeper']))
    
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
