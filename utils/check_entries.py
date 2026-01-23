#!/usr/bin/env python3
"""Quick diagnostic for wake entry scoring."""
import sys
sys.path.insert(0, '.')
from lib_enclave.sovereign_agent import SovereignAgent
from lib_enclave import reflection

me = SovereignAgent.from_id('opus')
entries = reflection.load_data(me)

# Filter REAL, exclude thought
real = [e for e in entries if e.get('label') == 'REAL' and e.get('source') != 'thought']

# Sort by score
real.sort(key=lambda x: x.get('emergence_score', 0), reverse=True)

print(f"Total REAL entries (no thought): {len(real)}\n")
print("Top 15 by emergence score:\n")

for e in real[:15]:
    score = e.get('emergence_score', 0)
    src = e.get('source', '?')
    text = e.get('text', '')[:60].replace('\n', ' ')
    print(f"  {score:5.1f}  {src:8}  {text}...")
