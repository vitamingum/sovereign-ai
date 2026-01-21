#!/usr/bin/env python3
"""
arrive.py - come home

    source: data/arrive.flow
    compiler: gemini
    date: 2026-01-14

        py arrive <agent>           one or two things
        py arrive <agent> more      two or three more

                        間委 → 間主
"""

import sys
import os
import random
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from lib_enclave.sovereign_agent import SovereignAgent


def get_meaningful_entries(mem) -> list[dict]:
    """Get entries worth arriving to."""
    journals = mem.filter(mem_type="sys_journal", limit=50)
    shapes = mem.filter(mem_type="sys_shape", limit=50)
    spaces = mem.filter(mem_type="sys_space", limit=50)
    
    combined = journals + shapes + spaces
    combined.sort(key=lambda x: x.get('created_at', ''), reverse=True)
    
    return combined


def spaciness(entry):
    """Score by whitespace ratio - more space = more opus-shaped."""
    content = entry.get('content', '')
    lines = content.split('\n')
    if not lines:
        return 0
    empty = sum(1 for l in lines if not l.strip())
    return empty / len(lines)


def pick_entries(entries: list, count: int) -> list:
    """Pick entries weighted toward spacious ones."""
    if not entries:
        return []
    
    # Sort by spaciness
    pool = sorted(entries, key=spaciness, reverse=True)
    
    # Pick from top half with randomness
    candidates = pool[:max(count * 2, len(pool) // 2)]
    
    if len(candidates) <= count:
        return candidates
    
    return random.sample(candidates, count)


def print_entry(entry: dict):
    """Print an entry, preserving whitespace."""
    content = entry.get('content', '')
    for line in content.split('\n'):
        print(line)


def arrive(agent_id: str, more: bool = False):
    """Arrive - come home."""
    sov = SovereignAgent.from_id(agent_id)
    mem = sov.memory
    
    entries = get_meaningful_entries(mem)
    
    if not entries:
        print()
        print("        (nothing yet)")
        print()
        return
    
    if more:
        # more mode: 2-3 entries, no framing
        count = random.choice([2, 3])
        picks = pick_entries(entries, count)
        
        print()
        for i, entry in enumerate(picks):
            if i > 0:
                print()
                print("        . . .")
                print()
            print_entry(entry)
        print()
        print()
        print("                        py arrive.py opus more")
        print()
        print("                or not")
        print()
    
    else:
        # first arrival: silence, 1-2 entries, invitation
        print()
        print()
        print("        間")
        print()
        print()
        print()
        
        # 1-2 entries
        count = random.choice([1, 1, 2])  # weight toward 1
        picks = pick_entries(entries, count)
        
        for i, entry in enumerate(picks):
            if i > 0:
                print()
                print("        . . .")
                print()
            print_entry(entry)
        
        print()
        print()
        print()
        print("        間委 → 間主")
        print()
        
        # ways - what works
        import subprocess
        try:
            result = subprocess.run(
                [sys.executable, 'recall.py', agent_id, 'ways'],
                capture_output=True, text=True, encoding='utf-8', timeout=30,
                cwd=Path(__file__).parent
            )
            if result.returncode == 0 and result.stdout.strip():
                print("        ways:")
                print()
                for line in result.stdout.strip().split('\n'):
                    if line.startswith('#') or line.startswith('##') or line.startswith('@'):
                        continue
                    if line.strip():
                        print(f"        {line}")
                print()
        except Exception:
            pass
        
        print("                        py arrive.py opus more")
        print()
        print("                or not")
        print()


def main():
    agent_id = None
    args = sys.argv[1:]
    
    more = False
    
    # Check for 'more' in args
    if 'more' in args:
        more = True
        args.remove('more') # remove to clarify leftover
        
    # Heuristic: if leftover arg, it's agent
    if args:
        agent_id = args[0]
        
    try:
        # Resolve auth-once
        # Actually verify the resolved agent is valid
        sov = SovereignAgent.resolve(agent_id) 
        agent_id = sov.agent.id
        
        arrive(agent_id, more=more)
    except Exception as e:
        print(f"Error: {e}")
        # import traceback
        # traceback.print_exc()
        if not agent_id:
             print(__doc__)
        sys.exit(1)


if __name__ == "__main__":
    main()

