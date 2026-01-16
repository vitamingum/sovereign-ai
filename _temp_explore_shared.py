#!/usr/bin/env python3
"""Temporary script to explore shared memory contents."""
import sys
sys.path.insert(0, '.')

from lib_enclave.sovereign_agent import SovereignAgent
from collections import defaultdict

me = SovereignAgent.from_id('sonnet')
mem = me.memory

# Get all entries (increase limit to see more)
all_entries = mem.filter(limit=200)

print(f'Total entries in shared memory: {len(all_entries)}\n')

# Group by type
by_type = defaultdict(list)
for entry in all_entries:
    mem_type = entry.get('mem_type', 'unknown')
    by_type[mem_type].append(entry)

print('By type:')
for mem_type, entries in sorted(by_type.items()):
    print(f'  {mem_type}: {len(entries)}')

# Show some samples of each type
print('\n--- Sample Entries ---')
for mem_type, entries in sorted(by_type.items()):
    print(f'\n{mem_type} (showing first 2):')
    for entry in entries[:2]:
        creator = entry.get('metadata', {}).get('creator', 'unknown')
        created = entry.get('created_at', '')[:10]
        content = entry.get('content', '')[:100]
        print(f'  [{created}] {creator}: {content}...')
