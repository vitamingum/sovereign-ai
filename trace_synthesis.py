#!/usr/bin/env python3
"""Trace synthesis search."""
import sys
sys.path.insert(0, '.')
from wake import load_passphrase
from enclave.semantic_memory import SemanticMemory

shared_dir, _, shared_pass, _ = load_passphrase('opus')
sm = SemanticMemory(shared_dir)
sm.unlock(shared_pass)

syntheses = sm.list_by_tag('synthesis')
target = 'topic:agency-autonomy'

print(f'Looking for tag: {target}')
print(f'Total syntheses: {len(syntheses)}')

found = 0
for s in syntheses:
    tags = s.get('tags', [])
    if target in tags:
        found += 1
        content = s.get('content', '')
        print(f'\nFOUND!')
        print(f'Tags: {tags}')
        print(f'Content: {content[:200]}')

print(f'\nTotal found with exact tag: {found}')

# Also check what tags contain 'agency-autonomy'
print("\nTags containing 'agency-autonomy':")
for s in syntheses:
    tags = s.get('tags', [])
    for t in tags:
        if 'agency-autonomy' in t.lower():
            print(f'  {t}')
            break
