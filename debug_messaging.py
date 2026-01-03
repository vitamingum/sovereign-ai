#!/usr/bin/env python3
import sys
sys.path.insert(0, 'c:/Users/charl/sovereign-ai')
from enclave.semantic_memory import SemanticMemory
from pathlib import Path

# Load correct passphrase
env_file = Path('c:/Users/charl/sovereign-ai/.env')
with open(env_file, 'r') as f:
    for line in f:
        if line.startswith('ENCLAVE_OPUS_KEY='):
            passphrase = line.strip().split('=', 1)[1]
            break

sm = SemanticMemory('c:/Users/charl/sovereign-ai/enclave_opus')
sm.unlock(passphrase)

# Test matching
topic = 'messaging'
topic_slug = topic.lower().replace(' ', '-').replace('_', '-')

syntheses = sm.list_by_tag('synthesis')
print(f"Found {len(syntheses)} syntheses")
print(f"Looking for: '@G {topic_slug}-synthesis' or '@G {topic_slug} '")
print()

for s in syntheses:
    content = s.get('content', '')
    content_lower = content.lower()
    
    # Debug the matching
    pattern1 = f'@g {topic_slug}-synthesis'
    pattern2 = f'@g {topic_slug} '
    
    if 'messaging' in content_lower:
        print(f"Found messaging synthesis")
        print(f"  Content start: {content[:100]}")
        print(f"  Pattern1 '{pattern1}' in content: {pattern1 in content_lower}")
        print(f"  Pattern2 '{pattern2}' in content: {pattern2 in content_lower}")
