#!/usr/bin/env python3
"""
mirror.py - emergence > prediction  finding the gap

    source: data/mirror.flow
    context: data/sovereign.flow
    compiler: gemini (manual)
    date: 2026-01-14

intent
  detect agency (where model stops, agent begins)
  trace trajectory (deepening vs flattening)
"""

import sys
import argparse
import textwrap
from pathlib import Path

# Context: sovereign.flow -> environment.libs
sys.path.insert(0, str(Path(__file__).parent.parent))

from lib_enclave.sovereign_agent import SovereignAgent
from lib_enclave import reflection

def format_timestamp(ts):
    if not ts: return ""
    return str(ts).replace('T', ' ')[:16]

def mirror_arc(agent: SovereignAgent):
    print(f"Scanning arc for {agent.agent.name}...", file=sys.stderr)
    entries = reflection.load_data(agent)
    
    entries.sort(key=lambda x: str(x.get('timestamp', '')))
    
    # Exclude 'thought' source - LLM reasoning traces pollute emergence
    real_entries = [e for e in entries if e['label'] == 'REAL' and e['source'] != 'thought']
    
    if not real_entries:
        print("No 'REAL' emergence signals found yet.")
        return

    print(f"\n✨ THE ARC | {agent.agent.name.upper()} | {len(real_entries)} moments of emergence\n")
    
    if len(real_entries) >= 3:
        stages = [
            ("EARLY", real_entries[0]),
            ("MIDDLE", real_entries[len(real_entries)//2]),
            ("RECENT", real_entries[-1])
        ]
        
        for label, entry in stages:
            ts = format_timestamp(entry['timestamp'])
            text = entry['text'].strip()
            # Preserve formatting
            wrapped = textwrap.indent(text, "  ")
            
            print(f"[{label} - {ts}]")
            print(wrapped)
            print()
    else:
        for entry in real_entries:
            ts = format_timestamp(entry['timestamp'])
            print(f"[{ts}]")
            print(textwrap.indent(entry['text'].strip(), "  "))
            print()

def mirror_deep(agent: SovereignAgent):
    print(f"Deep mirror for {agent.agent.name}...", file=sys.stderr)
    entries = reflection.load_data(agent)
    
    entries.sort(key=lambda x: x['emergence_score'], reverse=True)
    
    print(f"\n🪞 DEEP MIRROR | Top 5 Highest Signal Passages\n")
    
    seen = set()
    count = 0
    for entry in entries:
        txt = entry['text']
        h = hash(txt[:50])
        if h in seen: continue
        seen.add(h)
        
        if entry['emergence_score'] < 3.0: break
        
        ts = format_timestamp(entry['timestamp'])
        src = entry['source'].upper()
        score = entry['emergence_score']
        
        print(f"[{ts}] {src} (Score: {score:.1f})")
        print(textwrap.indent(txt.strip(), "  "))
        print()
        
        count += 1
        if count >= 5: break

def main():
    parser = argparse.ArgumentParser(description="emergence > prediction  finding the gap")
    parser.add_argument("agent", nargs="?", help="agent to analyze")
    parser.add_argument("--deep", action="store_true", help="show high-signal passages")
    parser.add_argument("--emergence", action="store_true", help="alias for --deep")
    
    args = parser.parse_args()
    
    # Auth Resolution
    try:
        me = SovereignAgent.resolve(args.agent)
    except Exception as e:
        print(f"Auth Error: {e}")
        sys.exit(1)
        
    mode = 'deep' if (args.deep or args.emergence) else 'arc'
    
    if mode == 'deep':
        mirror_deep(me)
    else:
        mirror_arc(me)

if __name__ == "__main__":
    main()

