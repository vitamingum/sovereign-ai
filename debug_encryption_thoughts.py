#!/usr/bin/env python3
import sys
sys.path.insert(0, 'c:/Users/charl/sovereign-ai')
from enclave.semantic_memory import SemanticMemory
from pathlib import Path

env_file = Path('c:/Users/charl/sovereign-ai/.env')
with open(env_file, 'r') as f:
    for line in f:
        if line.startswith('ENCLAVE_OPUS_KEY='):
            passphrase = line.strip().split('=', 1)[1]
            break

sm = SemanticMemory('c:/Users/charl/sovereign-ai/enclave_opus')
sm.unlock(passphrase)

# Get all thoughts and filter for encryption-related
thoughts = sm.list_by_tag('thought')
print(f'Total thoughts: {len(thoughts)}')
print()
print('=== ENCRYPTION-RELATED THOUGHTS ===')
keywords = ['encrypt', 'crypto', 'passphrase', 'key', 'privacy', 'secret', 'aes', 'ed25519']
for t in thoughts:
    content = t.get('content', '').lower()
    if any(kw in content for kw in keywords):
        text = t.get('content', '')[:300].replace('\n', ' ')
        print(f"• {text}")
        print()
