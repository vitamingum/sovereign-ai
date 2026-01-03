#!/usr/bin/env python3
"""Debug semantic memory list_all returning empty."""
import sys
import json
sys.path.insert(0, 'c:/Users/charl/sovereign-ai')
from enclave.semantic_memory import SemanticMemory

sm = SemanticMemory('c:/Users/charl/sovereign-ai/enclave_opus')
sm.unlock('copilot-opus-4.5-sovereign-2025')

log_file = sm.private_path / 'semantic_memories.jsonl'
with open(log_file, 'r', encoding='utf-8') as f:
    lines = f.readlines()
print(f'File has {len(lines)} lines')

# Check structure
mem = json.loads(lines[0])
print(f'First mem keys: {list(mem.keys())}')
print(f'Has content_nonce: {"content_nonce" in mem}')
print(f'Has encryption_key: {sm._encryption_key is not None}')

# Try manual decryption
if 'content_nonce' in mem:
    content_nonce = bytes.fromhex(mem['content_nonce'])
    content_ciphertext = bytes.fromhex(mem['content'])
    try:
        decrypted = sm._decrypt(content_nonce, content_ciphertext, sm._encryption_key)
        print(f'Decryption SUCCESS: {decrypted[:100]}')
    except Exception as e:
        import traceback
        print(f'Decryption FAILED: {e}')
        traceback.print_exc()
else:
    print('No content_nonce - checking content directly')
    print(f'Content sample: {mem.get("content", "NONE")[:100]}')
