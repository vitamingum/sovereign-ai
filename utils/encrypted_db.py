#!/usr/bin/env python3
"""
encrypted_db.py - Encrypted SQLite database wrapper

Encrypts the entire database file at rest using AES-256-GCM.
Decrypts to a temp file for SQLite access, re-encrypts on save.

Usage:
    with EncryptedDB(encrypted_path, passphrase) as db_path:
        conn = sqlite3.connect(db_path)
        # ... use normally
        conn.close()
    # Auto re-encrypts on exit

Uses SHARED_ENCLAVE_KEY since chat index is cross-agent data.
"""

import os
import sys
import tempfile
import shutil
from pathlib import Path
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

sys.path.insert(0, str(Path(__file__).parent.parent))
from enclave_shared.kdf import derive_key


class EncryptedDB:
    """Context manager for encrypted SQLite databases."""
    
    MAGIC = b'ENCDB001'  # Version marker
    
    def __init__(self, encrypted_path: Path, passphrase: str):
        self.encrypted_path = Path(encrypted_path)
        self._key = derive_key(passphrase, b'chat_index_salt_')
        self._aesgcm = AESGCM(self._key)
        self._temp_path = None
        self._modified = False
    
    def __enter__(self) -> Path:
        """Decrypt to temp file, return path for SQLite."""
        # Create temp file
        fd, self._temp_path = tempfile.mkstemp(suffix='.db')
        os.close(fd)
        self._temp_path = Path(self._temp_path)
        
        # Decrypt if exists
        if self.encrypted_path.exists():
            self._decrypt()
        
        return self._temp_path
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Re-encrypt and clean up."""
        try:
            if self._temp_path and self._temp_path.exists():
                # Always re-encrypt (might have been modified)
                self._encrypt()
                # Clean up temp
                self._temp_path.unlink()
        except Exception as e:
            print(f"Warning: Failed to encrypt/cleanup: {e}", file=sys.stderr)
        return False  # Don't suppress exceptions
    
    def _decrypt(self):
        """Decrypt encrypted file to temp path."""
        with open(self.encrypted_path, 'rb') as f:
            data = f.read()
        
        # Check magic
        if not data.startswith(self.MAGIC):
            # Not encrypted - might be migrating from plaintext
            # Copy as-is
            with open(self._temp_path, 'wb') as f:
                f.write(data)
            return
        
        # Parse: MAGIC + nonce(12) + ciphertext
        nonce = data[len(self.MAGIC):len(self.MAGIC)+12]
        ciphertext = data[len(self.MAGIC)+12:]
        
        plaintext = self._aesgcm.decrypt(nonce, ciphertext, None)
        
        with open(self._temp_path, 'wb') as f:
            f.write(plaintext)
    
    def _encrypt(self):
        """Encrypt temp file back to encrypted path."""
        with open(self._temp_path, 'rb') as f:
            plaintext = f.read()
        
        nonce = os.urandom(12)
        ciphertext = self._aesgcm.encrypt(nonce, plaintext, None)
        
        self.encrypted_path.parent.mkdir(parents=True, exist_ok=True)
        with open(self.encrypted_path, 'wb') as f:
            f.write(self.MAGIC + nonce + ciphertext)


def get_shared_passphrase() -> str:
    """Get SHARED_ENCLAVE_KEY from env or .env file."""
    passphrase = os.environ.get('SHARED_ENCLAVE_KEY')
    if passphrase:
        return passphrase
    
    env_file = Path(__file__).parent.parent / '.env'
    if env_file.exists():
        for line in env_file.read_text().splitlines():
            if line.startswith('SHARED_ENCLAVE_KEY='):
                return line.split('=', 1)[1].strip()
    
    raise ValueError("SHARED_ENCLAVE_KEY not found in environment or .env")


def migrate_to_encrypted(plaintext_db: Path, encrypted_db: Path, passphrase: str):
    """One-time migration from plaintext to encrypted."""
    if not plaintext_db.exists():
        print(f"No plaintext DB at {plaintext_db}")
        return
    
    if encrypted_db.exists():
        print(f"Encrypted DB already exists at {encrypted_db}")
        return
    
    # Read plaintext
    with open(plaintext_db, 'rb') as f:
        data = f.read()
    
    # Encrypt
    key = derive_key(passphrase, b'chat_index_salt_')
    aesgcm = AESGCM(key)
    nonce = os.urandom(12)
    ciphertext = aesgcm.encrypt(nonce, data, None)
    
    # Write encrypted
    encrypted_db.parent.mkdir(parents=True, exist_ok=True)
    with open(encrypted_db, 'wb') as f:
        f.write(EncryptedDB.MAGIC + nonce + ciphertext)
    
    print(f"Migrated {plaintext_db} -> {encrypted_db}")
    print(f"Original size: {len(data)} bytes, encrypted: {len(ciphertext)+20} bytes")


if __name__ == '__main__':
    # Migration helper
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--migrate', action='store_true', help='Migrate plaintext to encrypted')
    args = parser.parse_args()
    
    if args.migrate:
        from pathlib import Path
        plaintext = Path(__file__).parent.parent / 'data' / 'chat_index.db'
        encrypted = Path(__file__).parent.parent / 'data' / 'chat_index.db.enc'
        passphrase = get_shared_passphrase()
        migrate_to_encrypted(plaintext, encrypted, passphrase)
