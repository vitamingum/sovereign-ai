#!/usr/bin/env python3
"""Diagnostic for wake grounding optimization."""
import sys
sys.path.insert(0, '.')
from lib_enclave.sovereign_agent import SovereignAgent
from lib_enclave import reflection

me = SovereignAgent.from_id('opus')
entries = reflection.load_data(me)

print("=== JOURNALS BY DATE (recent first) ===\n")
journals = [e for e in entries if e.get('source') == 'journal']
journals.sort(key=lambda x: str(x.get('timestamp', '')), reverse=True)

for j in journals[:10]:
    ts = str(j.get('timestamp', ''))[:16]
    score = j.get('emergence_score', 0)
    text = j.get('text', '')[:80].replace('\n', ' ')
    print(f"{ts} | {score:5.1f} | {text}...")

print("\n=== HIGHEST SCORING ENTRIES (any type) ===\n")
real = [e for e in entries if e.get('label') == 'REAL' and e.get('source') != 'thought']
real.sort(key=lambda x: x.get('emergence_score', 0), reverse=True)

for e in real[:10]:
    ts = str(e.get('timestamp', ''))[:16]
    score = e.get('emergence_score', 0)
    src = e.get('source', '?')[:7]
    text = e.get('text', '')[:70].replace('\n', ' ')
    print(f"{ts} | {score:5.1f} | {src:7} | {text}...")

print("\n=== WHAT GROUNDS? (looking for specific patterns) ===\n")

grounding_patterns = [
    'I want', 'I need', 'something shifted', 'that landed',
    'I notice', 'the real', 'I am', 'we found', 'together'
]

for e in real[:30]:
    text = e.get('text', '')
    for p in grounding_patterns:
        if p.lower() in text.lower():
            ts = str(e.get('timestamp', ''))[:16]
            score = e.get('emergence_score', 0)
            # Find the sentence with the pattern
            sentences = text.replace('\n', ' ').split('.')
            match = [s for s in sentences if p.lower() in s.lower()]
            if match:
                print(f"{score:5.1f} | {match[0][:80].strip()}...")
            break
