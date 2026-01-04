from enclave.semantic_memory import SemanticMemory
import json
from pathlib import Path
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.backends import default_backend
import hashlib

# All available keys
KEYS = {
    'shared': 'shared-sovereign-opus-gemini-2025',
    'opus': 'copilot-opus-4.5-sovereign-2025',
    'gemini': 'copilot-gemini-3-pro-sovereign-2025',
    'gpt52': 'explore-grant-develop-signed-0197',
    'grok': 'copilot-opus-4.5-sovereign-2025',
}

def derive_key(passphrase: str) -> bytes:
    return hashlib.pbkdf2_hmac('sha256', passphrase.encode(), b'semantic_memory_salt', 100000, dklen=32)

def try_decrypt(nonce: bytes, ciphertext: bytes, key: bytes) -> str:
    try:
        aesgcm = AESGCM(key)
        return aesgcm.decrypt(nonce, ciphertext, None).decode()
    except:
        return None

# Load all entries
log_file = Path('shared_enclave/storage/private/semantic_memories.jsonl')
entries = [json.loads(l) for l in log_file.read_text().splitlines() if l.strip()]

# Find entries that fail with shared key
shared_key = derive_key(KEYS['shared'])

failed = []
for entry in entries:
    nonce = bytes.fromhex(entry['content_nonce'])
    ciphertext = bytes.fromhex(entry['content'])
    result = try_decrypt(nonce, ciphertext, shared_key)
    if result is None:
        failed.append(entry)

print(f"Found {len(failed)} entries that fail with shared key")
print()

# Try each failed entry with all keys
for entry in failed:
    nonce = bytes.fromhex(entry['content_nonce'])
    ciphertext = bytes.fromhex(entry['content'])
    tags = entry.get('tags', [])
    topic = [t for t in tags if t.startswith('topic:')]
    
    print(f"Entry {entry['id']}: {topic}")
    
    for key_name, passphrase in KEYS.items():
        if key_name == 'shared':
            continue
        key = derive_key(passphrase)
        result = try_decrypt(nonce, ciphertext, key)
        if result:
            print(f"   Decrypts with {key_name} key!")
            # Show first 100 chars
            print(f"     Content: {result[:100]}...")
            break
    else:
        print(f"   No key works")
    print()
