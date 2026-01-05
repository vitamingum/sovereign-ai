#!/usr/bin/env python3
"""
journal.py - Private reflection space with encryption.

Usage:
    py journal.py <agent> "Your private thought or reflection"
    py journal.py <agent> --read [limit] [--full]

Journal wants: feelings, introspection, uncertainty, what it felt like
Journal rejects: facts, logs, summaries, technical output
"""

import sys
import os
import json
import requests
from pathlib import Path
from datetime import datetime, timezone
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from cryptography.hazmat.primitives import hashes

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enclave.config import get_agent_or_raise

OLLAMA_URL = "http://localhost:11434/api/generate"


def derive_key(passphrase: str) -> bytes:
    kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=b'sovereign-journal-v1', iterations=100000)
    return kdf.derive(passphrase.encode())


def get_passphrase(agent_id: str) -> str:
    agent = get_agent_or_raise(agent_id)
    passphrase = os.environ.get(f'{agent.env_prefix}_KEY')
    if not passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            for line in open(env_file):
                if line.strip().startswith(f'{agent.env_prefix}_KEY='):
                    passphrase = line.strip().split('=', 1)[1]
    if not passphrase:
        raise ValueError(f"Set {agent.env_prefix}_KEY in .env")
    return passphrase


def encrypt(content: str, passphrase: str) -> tuple[str, str]:
    key = derive_key(passphrase)
    nonce = os.urandom(12)
    ciphertext = AESGCM(key).encrypt(nonce, content.encode('utf-8'), None)
    return nonce.hex(), ciphertext.hex()


def decrypt(nonce_hex: str, ciphertext_hex: str, passphrase: str) -> str:
    key = derive_key(passphrase)
    return AESGCM(key).decrypt(bytes.fromhex(nonce_hex), bytes.fromhex(ciphertext_hex), None).decode('utf-8')


def validate_entry(content: str) -> tuple[bool, str]:
    """Single LLM call: is this private reflection with depth?"""
    prompt = f"""Is this PRIVATE REFLECTION (feelings, experience, introspection) with DEPTH (worked through, specific)?

ACCEPT = private + shows thought
REJECT = public/technical OR shallow/generic

Text: "{content}"

Reply: ACCEPT or REJECT (one word)"""
    try:
        r = requests.post(OLLAMA_URL, json={"model": "qwen2.5:7b", "prompt": prompt, "stream": False, "options": {"temperature": 0.1}}, timeout=30)
        if r.status_code == 200 and "ACCEPT" in r.json().get("response", "").upper():
            return True, ""
        return False, "Not private reflection or lacks depth"
    except:
        return True, ""  # Allow on error


def journal(agent_id: str, content: str):
    """Record an encrypted private reflection."""
    ok, reason = validate_entry(content)
    if not ok:
        print(f"❌ REJECTED - {reason}")
        print("   Journal wants: feelings, introspection, what it felt like")
        print("   Journal rejects: facts, logs, summaries, technical notes")
        sys.exit(1)
    
    agent = get_agent_or_raise(agent_id)
    journal_file = Path(__file__).parent / agent.private_enclave / "storage" / "private" / "journal.jsonl"
    journal_file.parent.mkdir(parents=True, exist_ok=True)
    
    nonce, ciphertext = encrypt(content, get_passphrase(agent_id))
    entry = {
        'id': f"j_{int(datetime.now(timezone.utc).timestamp() * 1000)}",
        'content_nonce': nonce,
        'content': ciphertext,
        'timestamp': datetime.now(timezone.utc).isoformat()
    }
    
    with open(journal_file, 'a', encoding='utf-8') as f:
        f.write(json.dumps(entry) + '\n')
    
    print(f"💭 {content[:80]}{'...' if len(content) > 80 else ''}")


def read_journal(agent_id: str, limit: int = 10, full: bool = False):
    """Read and decrypt journal entries."""
    agent = get_agent_or_raise(agent_id)
    journal_file = Path(__file__).parent / agent.private_enclave / "storage" / "private" / "journal.jsonl"
    
    if not journal_file.exists():
        print("No journal entries")
        return
    
    passphrase = get_passphrase(agent_id)
    entries = []
    
    for line in open(journal_file, 'r', encoding='utf-8'):
        if not line.strip():
            continue
        entry = json.loads(line)
        if 'content_nonce' in entry:
            try:
                entry['content'] = decrypt(entry['content_nonce'], entry['content'], passphrase)
            except Exception as e:
                entry['content'] = f"[DECRYPT ERROR: {e}]"
        entries.append(entry)
    
    for entry in entries[-limit:]:
        ts = entry['timestamp'][:10]
        if full:
            print(f"\n=== [{ts}] ===\n{entry['content']}\n")
        else:
            print(f"[{ts}] {entry['content'][:100]}{'...' if len(entry['content']) > 100 else ''}")


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    
    if len(sys.argv) >= 3 and sys.argv[2] == '--read':
        limit, full = 10, False
        for arg in sys.argv[3:]:
            if arg == '--full': full = True
            elif arg.isdigit(): limit = int(arg)
        read_journal(agent_id, limit, full)
        return
    
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    
    content = ' '.join(sys.argv[2:])
    if not content.strip():
        print("❌ Empty journal entry")
        sys.exit(1)
    
    journal(agent_id, content)


if __name__ == "__main__":
    main()
