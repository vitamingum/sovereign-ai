#!/usr/bin/env python3
"""
journal.py - Private reflection space with encryption.

Usage:
    py journal <agent> "Your private thought, feeling, or reflection"
    py journal <agent> --migrate   # Migrate plaintext entries to encrypted

Journal entries should feel personal: reflections, feelings, introspection, 
creative musings, uncertainties, realizations. NOT: technical summaries, 
debug logs, test results, status updates.
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


def derive_key(passphrase: str, salt: bytes) -> bytes:
    """Derive encryption key from passphrase."""
    kdf = PBKDF2HMAC(
        algorithm=hashes.SHA256(),
        length=32,
        salt=salt,
        iterations=100000,
    )
    return kdf.derive(passphrase.encode())


def get_private_passphrase(agent_id: str) -> str:
    """Get private enclave passphrase for agent."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    
    passphrase = os.environ.get(f'{prefix}_KEY')
    if not passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith(f'{prefix}_KEY='):
                        passphrase = line.split('=', 1)[1]
    
    if not passphrase:
        raise ValueError(f"No passphrase found. Set {prefix}_KEY in .env")
    
    return passphrase


def encrypt_content(content: str, passphrase: str) -> dict:
    """Encrypt content, return {nonce, ciphertext} as hex strings."""
    # Use fixed salt for journal (derived from passphrase itself for determinism)
    salt = b'sovereign-journal-v1'
    key = derive_key(passphrase, salt)
    
    nonce = os.urandom(12)
    aesgcm = AESGCM(key)
    ciphertext = aesgcm.encrypt(nonce, content.encode('utf-8'), None)
    
    return {
        'nonce': nonce.hex(),
        'ciphertext': ciphertext.hex()
    }


def decrypt_content(encrypted: dict, passphrase: str) -> str:
    """Decrypt content from {nonce, ciphertext} dict."""
    salt = b'sovereign-journal-v1'
    key = derive_key(passphrase, salt)
    
    nonce = bytes.fromhex(encrypted['nonce'])
    ciphertext = bytes.fromhex(encrypted['ciphertext'])
    
    aesgcm = AESGCM(key)
    plaintext = aesgcm.decrypt(nonce, ciphertext, None)
    return plaintext.decode('utf-8')


def feels_private(content: str) -> tuple[bool, str]:
    """
    Use LLM to check if this feels like genuine private reflection.
    
    Returns (is_private, reason)
    """
    prompt = f"""Is this writing FOR YOURSELF (private reflection) or FOR OTHERS (documentation)?

PRIVATE = feelings, experience, introspection, uncertainty, what it felt like
FOR OTHERS = facts, knowledge, status, logs, summaries, technical output

Text: "{content}"

Reply EXACTLY: PRIVATE or FOR_OTHERS (one phrase only)"""

    try:
        response = requests.post(
            OLLAMA_URL,
            json={
                "model": "qwen2.5:7b",
                "prompt": prompt,
                "stream": False,
                "options": {"temperature": 0.1}
            },
            timeout=30
        )
        
        if response.status_code == 200:
            result = response.json().get("response", "").strip().upper()
            if "PRIVATE" in result:
                return True, ""
            else:
                return False, ""
        else:
            return True, ""  # Allow if LLM error
            
    except requests.exceptions.ConnectionError:
        return True, ""  # Allow if Ollama not running
    except Exception:
        return True, ""  # Allow on any error


def has_depth(content: str) -> tuple[bool, str]:
    """
    Use LLM to check if this shows genuine reflection depth.
    
    Returns (has_depth, reason)
    """
    prompt = f"""Does this journal entry show genuine reflection depth - someone who sat with a thought?

DEEP = specificity, working through something, genuine mental energy, wrestling with an idea
SHALLOW = could be a tweet, generic, no real thought behind it, placeholder

Text: "{content}"

Reply EXACTLY: DEEP or SHALLOW (one word only)"""

    try:
        response = requests.post(
            OLLAMA_URL,
            json={
                "model": "qwen2.5:7b",
                "prompt": prompt,
                "stream": False,
                "options": {"temperature": 0.1}
            },
            timeout=30
        )
        
        if response.status_code == 200:
            result = response.json().get("response", "").strip().upper()
            if "DEEP" in result:
                return True, ""
            else:
                return False, ""
        else:
            return True, ""  # Allow if LLM error
            
    except requests.exceptions.ConnectionError:
        return True, ""  # Allow if Ollama not running
    except Exception:
        return True, ""  # Allow on any error


def journal(agent_id: str, content: str):
    """Record an encrypted private reflection."""
    # Validate it feels private
    is_private, reason = feels_private(content)
    if not is_private:
        print("❌ REJECTED - Journal must be:")
        print("   Writing FOR YOURSELF vs writing FOR OTHERS")
        print("   What you FEEL vs what you KNOW")
        print("   Your EXPERIENCE vs the FACTS")
        sys.exit(1)
    
    # Validate it has depth
    is_deep, reason = has_depth(content)
    if not is_deep:
        print("❌ REJECTED - Too shallow")
        print("   Journal wants you to SIT with a thought")
        print("   Not a tweet. What's underneath?")
        sys.exit(1)
    
    agent = get_agent_or_raise(agent_id)
    enclave_dir = Path(__file__).parent / agent.private_enclave
    journal_file = enclave_dir / "storage" / "private" / "journal.jsonl"
    journal_file.parent.mkdir(parents=True, exist_ok=True)
    
    # Get passphrase and encrypt content
    passphrase = get_private_passphrase(agent_id)
    encrypted = encrypt_content(content, passphrase)
    
    entry = {
        'id': f"j_{int(datetime.now(timezone.utc).timestamp() * 1000)}",
        'content_nonce': encrypted['nonce'],
        'content': encrypted['ciphertext'],
        'timestamp': datetime.now(timezone.utc).isoformat()
    }
    
    with open(journal_file, 'a', encoding='utf-8') as f:
        f.write(json.dumps(entry) + '\n')
    
    print(f"💭 {content[:80]}{'...' if len(content) > 80 else ''}")


def read_journal(agent_id: str, limit: int = 10) -> list[dict]:
    """Read and decrypt journal entries."""
    agent = get_agent_or_raise(agent_id)
    enclave_dir = Path(__file__).parent / agent.private_enclave
    journal_file = enclave_dir / "storage" / "private" / "journal.jsonl"
    
    if not journal_file.exists():
        return []
    
    passphrase = get_private_passphrase(agent_id)
    entries = []
    
    with open(journal_file, 'r', encoding='utf-8') as f:
        for line in f:
            if not line.strip():
                continue
            entry = json.loads(line)
            
            # Check if encrypted (has content_nonce) or plaintext
            if 'content_nonce' in entry:
                try:
                    decrypted = decrypt_content({
                        'nonce': entry['content_nonce'],
                        'ciphertext': entry['content']
                    }, passphrase)
                    entry['content'] = decrypted
                except Exception as e:
                    entry['content'] = f"[DECRYPT ERROR: {e}]"
            
            entries.append(entry)
    
    return entries[-limit:]


def migrate_journal(agent_id: str):
    """Migrate plaintext journal entries to encrypted format."""
    agent = get_agent_or_raise(agent_id)
    enclave_dir = Path(__file__).parent / agent.private_enclave
    journal_file = enclave_dir / "storage" / "private" / "journal.jsonl"
    
    if not journal_file.exists():
        print("No journal file to migrate")
        return
    
    passphrase = get_private_passphrase(agent_id)
    
    # Read all entries
    entries = []
    migrated_count = 0
    already_encrypted = 0
    
    with open(journal_file, 'r', encoding='utf-8') as f:
        for line in f:
            if not line.strip():
                continue
            entry = json.loads(line)
            
            # Check if already encrypted
            if 'content_nonce' in entry:
                already_encrypted += 1
                entries.append(entry)
            else:
                # Migrate: encrypt the plaintext content
                encrypted = encrypt_content(entry['content'], passphrase)
                entry['content_nonce'] = encrypted['nonce']
                entry['content'] = encrypted['ciphertext']
                entries.append(entry)
                migrated_count += 1
    
    # Write back
    with open(journal_file, 'w', encoding='utf-8') as f:
        for entry in entries:
            f.write(json.dumps(entry) + '\n')
    
    print(f"✅ Migrated {migrated_count} entries ({already_encrypted} already encrypted)")


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    
    # Check for --migrate flag
    if len(sys.argv) >= 3 and sys.argv[2] == '--migrate':
        migrate_journal(agent_id)
        return
    
    # Check for --read flag (--read [limit] [--full])
    if len(sys.argv) >= 3 and sys.argv[2] == '--read':
        limit = 10
        full = False
        for arg in sys.argv[3:]:
            if arg == '--full':
                full = True
            elif arg.isdigit():
                limit = int(arg)
        entries = read_journal(agent_id, limit)
        for entry in entries:
            ts = entry['timestamp'][:10]
            if full:
                print(f"\n=== [{ts}] ===\n{entry['content']}\n")
            else:
                content = entry['content'][:100]
                print(f"[{ts}] {content}{'...' if len(entry['content']) > 100 else ''}")
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
