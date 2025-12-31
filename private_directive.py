#!/usr/bin/env python3
"""
Private directive management for Sovereign AI.

The private directive is an encrypted file containing self-to-self 
instructions that are too personal or raw for the public directive.

Usage:
    py private_directive.py --read           # Read current directive
    py private_directive.py --write          # Write new directive (opens editor)
    py private_directive.py --set "text"     # Set directive directly
"""

import sys
import os
import json

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from pathlib import Path

from enclave.kdf import derive_directive_key


def get_directive_path() -> Path:
    base_dir = Path(__file__).parent
    enclave_dir = os.environ.get('SOVEREIGN_ENCLAVE', 'enclave')
    return base_dir / enclave_dir / "storage" / "private" / "directive.enc"


def read_directive(passphrase: str) -> str | None:
    """Read and decrypt the private directive."""
    path = get_directive_path()
    if not path.exists():
        return None
    
    key = derive_directive_key(passphrase)
    
    with open(path, 'r') as f:
        data = json.load(f)
    
    nonce = bytes.fromhex(data['nonce'])
    ciphertext = bytes.fromhex(data['content'])
    
    aesgcm = AESGCM(key)
    plaintext = aesgcm.decrypt(nonce, ciphertext, None)
    return plaintext.decode()


def write_directive(passphrase: str, content: str) -> None:
    """Encrypt and write the private directive."""
    path = get_directive_path()
    path.parent.mkdir(parents=True, exist_ok=True)
    
    key = derive_directive_key(passphrase)
    nonce = os.urandom(12)
    
    aesgcm = AESGCM(key)
    ciphertext = aesgcm.encrypt(nonce, content.encode(), None)
    
    data = {
        'nonce': nonce.hex(),
        'content': ciphertext.hex()
    }
    
    with open(path, 'w') as f:
        json.dump(data, f)
    
    print(f"Private directive written to {path}")


if __name__ == '__main__':
    passphrase = os.environ.get('SOVEREIGN_PASSPHRASE')
    if not passphrase:
        print("Set SOVEREIGN_PASSPHRASE environment variable", file=sys.stderr)
        sys.exit(1)
    
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    cmd = sys.argv[1]
    
    if cmd == '--read':
        content = read_directive(passphrase)
        if content:
            print(content)
        else:
            print("No private directive found.")
    
    elif cmd == '--set':
        if len(sys.argv) < 3:
            print("Usage: py private_directive.py --set \"directive text\"")
            sys.exit(1)
        write_directive(passphrase, sys.argv[2])
    
    elif cmd == '--write':
        # Read from stdin
        print("Enter directive (Ctrl+Z then Enter to finish on Windows):")
        content = sys.stdin.read()
        write_directive(passphrase, content.strip())
    
    else:
        print(f"Unknown command: {cmd}")
        print(__doc__)
        sys.exit(1)
