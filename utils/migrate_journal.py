#!/usr/bin/env python3
"""Migrate plaintext journal entries to encrypted format."""

import sys
import os
import json
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from cryptography.hazmat.primitives import hashes
from enclave.config import get_agent_or_raise


def derive_key(passphrase: str, salt: bytes) -> bytes:
    kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=100000)
    return kdf.derive(passphrase.encode())


def encrypt_content(content: str, passphrase: str) -> dict:
    salt = b'sovereign-journal-v1'
    key = derive_key(passphrase, salt)
    nonce = os.urandom(12)
    aesgcm = AESGCM(key)
    ciphertext = aesgcm.encrypt(nonce, content.encode('utf-8'), None)
    return {'nonce': nonce.hex(), 'ciphertext': ciphertext.hex()}


def get_private_passphrase(agent_id: str) -> str:
    agent = get_agent_or_raise(agent_id)
    passphrase = os.environ.get(f'{agent.env_prefix}_KEY')
    if not passphrase:
        env_file = Path(__file__).parent.parent / '.env'
        if env_file.exists():
            for line in open(env_file):
                if line.strip().startswith(f'{agent.env_prefix}_KEY='):
                    passphrase = line.strip().split('=', 1)[1]
    if not passphrase:
        raise ValueError(f"No passphrase. Set {agent.env_prefix}_KEY in .env")
    return passphrase


def migrate_journal(agent_id: str):
    """Migrate plaintext journal entries to encrypted format."""
    agent = get_agent_or_raise(agent_id)
    journal_file = Path(__file__).parent.parent / agent.private_enclave / "storage" / "private" / "journal.jsonl"
    
    if not journal_file.exists():
        print("No journal file to migrate")
        return
    
    passphrase = get_private_passphrase(agent_id)
    entries = []
    migrated_count = 0
    already_encrypted = 0
    
    for line in open(journal_file, 'r', encoding='utf-8'):
        if not line.strip():
            continue
        entry = json.loads(line)
        if 'content_nonce' in entry:
            already_encrypted += 1
            entries.append(entry)
        else:
            encrypted = encrypt_content(entry['content'], passphrase)
            entry['content_nonce'] = encrypted['nonce']
            entry['content'] = encrypted['ciphertext']
            entries.append(entry)
            migrated_count += 1
    
    with open(journal_file, 'w', encoding='utf-8') as f:
        for entry in entries:
            f.write(json.dumps(entry) + '\n')
    
    print(f"✅ Migrated {migrated_count} entries ({already_encrypted} already encrypted)")


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: py utils/migrate_journal.py <agent>")
        sys.exit(1)
    migrate_journal(sys.argv[1])
