#!/usr/bin/env python3
"""Check which entries fail decryption and show their metadata."""
import json, sys, os
sys.path.insert(0, '.')
from pathlib import Path
from dotenv import load_dotenv
load_dotenv()

from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from enclave.kdf import derive_memory_key

# Get shared key
shared_key = os.environ.get('SHARED_ENCLAVE_KEY')
if not shared_key:
    with open('.env') as f:
        for line in f:
            if line.startswith('SHARED_ENCLAVE_KEY='):
                shared_key = line.split('=',1)[1].strip()

key = derive_memory_key(shared_key)

log_file = Path('shared_enclave/storage/private/semantic_memories.jsonl')
entries = []
with open(log_file) as f:
    for line in f:
        if line.strip():
            entries.append(json.loads(line))

failures = []
for e in entries:
    try:
        nonce = bytes.fromhex(e['content_nonce'])
        ctext = bytes.fromhex(e['content'])
        aesgcm = AESGCM(key)
        aesgcm.decrypt(nonce, ctext, None)
    except:
        failures.append(e)

print(f'Failed to decrypt: {len(failures)} / {len(entries)}')
print()
for f in failures:
    print(f"ID: {f['id']}")
    print(f"  Time: {f['timestamp'][:19]}")
    print(f"  Tags: {f['tags']}")
    print()
