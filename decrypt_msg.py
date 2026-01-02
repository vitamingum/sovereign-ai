#!/usr/bin/env python3
import json
from pathlib import Path
import sys
sys.path.insert(0, '.')
from enclave.crypto import SovereignIdentity
from enclave.config import get_agent_or_raise
from enclave.opaque import OpaqueStorage
from enclave.hardware import get_enclave
import os
from cryptography.hazmat.primitives import serialization

agent = get_agent_or_raise('opus')
enclave_path = Path(agent.enclave)

# Try hardware enclave first
key_file = enclave_path / "storage" / "private" / "key.sealed"
passphrase = None
if key_file.exists():
    try:
        with open(key_file, "rb") as f:
            sealed_data = f.read()
        hw_enclave = get_enclave()
        passphrase = hw_enclave.unseal(sealed_data).decode('utf-8')
    except Exception as e:
        print(f"Hardware enclave failed: {e}")

if not passphrase:
    passphrase = os.environ.get('OPUS_KEY') or os.environ.get('SOVEREIGN_PASSPHRASE')
    if not passphrase:
        with open('.env') as f:
            for line in f:
                if line.startswith('OPUS_KEY='):
                    passphrase = line.strip().split('=',1)[1]
                    break

print(f"Passphrase found: {bool(passphrase)}")

identity = SovereignIdentity(enclave_path)
if not identity.unlock(passphrase):
    print("Failed to unlock identity")
    sys.exit(1)

# Get raw private key
sk_bytes = identity._private_key.private_bytes(
    encoding=serialization.Encoding.Raw,
    format=serialization.PrivateFormat.Raw,
    encryption_algorithm=serialization.NoEncryption()
)

msgs = sorted(Path('messages').glob('*gemini*.json'), key=lambda p: p.stat().st_mtime, reverse=True)
for m in msgs[:3]:
    with open(m) as f:
        data = json.load(f)
    if data.get('to') == 'opus':
        try:
            encrypted_bundle = json.loads(data['content'])
            plaintext_bytes = OpaqueStorage.decrypt_share(encrypted_bundle, sk_bytes)
            plaintext = plaintext_bytes.decode('utf-8')
            print(f"=== From: {data['from']} ===")
            print(plaintext)
            print()
        except Exception as e:
            print(f"Cannot decrypt {m.name}: {e}")
        break
