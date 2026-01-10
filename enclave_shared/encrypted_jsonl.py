"""
Sovereign AI Enclave - Encrypted JSONL Storage

Provides encrypted-at-rest storage for line-oriented JSON files.
Uses AES-256-GCM with key derived from agent passphrase.

Design:
- Each line is encrypted separately for append-friendliness
- Nonce stored with each line (hex:ciphertext format)
- Compatible with existing file locations
"""

import os
import json
from pathlib import Path
from typing import List, Iterator, Optional
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from .kdf import derive_key


class EncryptedJSONL:
    """
    Encrypted JSONL file handler.
    
    Format: Each line is "nonce_hex:ciphertext_hex\n"
    
    Usage:
        ejsonl = EncryptedJSONL(path, passphrase, salt)
        ejsonl.append({"type": "intention", "content": "..."})
        for record in ejsonl.read_all():
            print(record)
    """
    
    def __init__(self, path: Path, passphrase: str, salt: bytes = None):
        self.path = Path(path)
        # Use file path as additional salt to prevent key reuse across files
        file_salt = self.path.name.encode('utf-8')
        combined_salt = (salt or b'') + file_salt
        # Pad or truncate to 16 bytes for derive_key
        combined_salt = (combined_salt + b'\x00' * 16)[:16]
        self._key = derive_key(passphrase, combined_salt)
        self._aesgcm = AESGCM(self._key)
        
    def append(self, record: dict) -> None:
        """Append an encrypted record."""
        self.path.parent.mkdir(parents=True, exist_ok=True)
        
        plaintext = json.dumps(record, ensure_ascii=False).encode('utf-8')
        nonce = os.urandom(12)
        ciphertext = self._aesgcm.encrypt(nonce, plaintext, None)
        
        line = f"{nonce.hex()}:{ciphertext.hex()}\n"
        
        with open(self.path, 'a', encoding='utf-8') as f:
            f.write(line)
    
    def read_all(self) -> List[dict]:
        """Read and decrypt all records."""
        if not self.path.exists():
            return []
        
        records = []
        with open(self.path, 'r', encoding='utf-8') as f:
            for line_num, line in enumerate(f, 1):
                line = line.strip()
                if not line:
                    continue
                try:
                    record = self._decrypt_line(line)
                    records.append(record)
                except Exception as e:
                    # Log but continue - don't fail on corrupted lines
                    print(f"Warning: Could not decrypt line {line_num}: {e}")
        return records
    
    def read_last_n(self, n: int) -> List[dict]:
        """Read last N records (efficient for tailing)."""
        all_records = self.read_all()
        return all_records[-n:] if n < len(all_records) else all_records
    
    def _decrypt_line(self, line: str) -> dict:
        """Decrypt a single line."""
        if ':' not in line:
            # Might be legacy plaintext - try to parse as JSON
            return json.loads(line)
        
        nonce_hex, ciphertext_hex = line.split(':', 1)
        nonce = bytes.fromhex(nonce_hex)
        ciphertext = bytes.fromhex(ciphertext_hex)
        
        plaintext = self._aesgcm.decrypt(nonce, ciphertext, None)
        return json.loads(plaintext.decode('utf-8'))
    
    def migrate_plaintext(self, plaintext_path: Path = None) -> int:
        """
        Migrate existing plaintext JSONL to encrypted format.
        
        Args:
            plaintext_path: Path to plaintext file. If None, infers from self.path
                           by removing .enc from the name.
        
        Returns number of records migrated.
        Creates backup at {plaintext_path}.bak
        """
        if plaintext_path is None:
            # Infer: intentions.enc.jsonl -> intentions.jsonl
            name = self.path.name.replace('.enc.jsonl', '.jsonl')
            plaintext_path = self.path.parent / name
        
        plaintext_path = Path(plaintext_path)
        
        if not plaintext_path.exists():
            return 0
        
        # Check if already migrated (encrypted file exists and has content)
        if self.path.exists():
            try:
                existing = self.read_all()
                if existing:
                    return 0  # Already have encrypted data
            except:
                pass
        
        # Read plaintext records
        plaintext_records = []
        with open(plaintext_path, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    plaintext_records.append(json.loads(line))
                except json.JSONDecodeError:
                    continue
        
        if not plaintext_records:
            return 0
        
        # Backup original
        backup_path = plaintext_path.with_suffix('.jsonl.bak')
        if not backup_path.exists():
            import shutil
            shutil.copy(plaintext_path, backup_path)
        
        # Write encrypted
        for record in plaintext_records:
            self.append(record)
        
        return len(plaintext_records)


def get_encrypted_intentions(enclave_path: Path, passphrase: str) -> EncryptedJSONL:
    """Get encrypted intentions handler for an enclave."""
    path = enclave_path / "storage" / "private" / "intentions.enc.jsonl"
    return EncryptedJSONL(path, passphrase)


def get_encrypted_journal(enclave_path: Path, passphrase: str) -> EncryptedJSONL:
    """Get encrypted journal handler for an enclave."""
    path = enclave_path / "storage" / "private" / "journal.enc.jsonl"
    return EncryptedJSONL(path, passphrase)
