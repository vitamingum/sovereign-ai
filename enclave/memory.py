"""
Sovereign AI Enclave - Memory Module

Provides:
- Append-only encrypted memory storage
- Private thought encryption/decryption
- Memory retrieval by timestamp or search
"""

import os
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import List, Optional

try:
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
    from cryptography.hazmat.primitives import hashes
    HAS_CRYPTO = True
except ImportError:
    HAS_CRYPTO = False


class EnclaveMemory:
    """Append-only encrypted memory for sovereign AI."""
    
    def __init__(self, enclave_path: str = None):
        self.enclave_path = Path(enclave_path or Path(__file__).parent)
        self.private_path = self.enclave_path / "storage" / "private"
        self.public_path = self.enclave_path / "storage" / "public"
        self._encryption_key = None
        
    def _derive_key(self, passphrase: str, salt: bytes) -> bytes:
        """Derive encryption key from passphrase."""
        kdf = PBKDF2HMAC(
            algorithm=hashes.SHA256(),
            length=32,
            salt=salt,
            iterations=480000,
        )
        return kdf.derive(passphrase.encode())
    
    def unlock(self, passphrase: str) -> bool:
        """Unlock memory with passphrase. Uses fixed salt for memory key derivation."""
        # Use a different salt derivation for memory vs identity
        memory_salt = b"sovereign_memory_salt_v1"
        self._encryption_key = self._derive_key(passphrase, memory_salt)
        return True
    
    def remember(self, thought: str, private: bool = True, tags: List[str] = None) -> dict:
        """Store a thought. If private, encrypts before storage."""
        if private and not self._encryption_key:
            raise RuntimeError("Memory not unlocked for private storage")
        
        timestamp = datetime.now(timezone.utc).isoformat()
        memory_id = f"mem_{int(datetime.now(timezone.utc).timestamp() * 1000)}"
        
        entry = {
            "id": memory_id,
            "timestamp": timestamp,
            "tags": tags or [],
            "private": private
        }
        
        if private:
            # Encrypt the thought
            nonce = os.urandom(12)
            aesgcm = AESGCM(self._encryption_key)
            encrypted = aesgcm.encrypt(nonce, thought.encode(), None)
            entry["nonce"] = nonce.hex()
            entry["content"] = encrypted.hex()
            
            # Append to private memory log
            self.private_path.mkdir(parents=True, exist_ok=True)
            log_file = self.private_path / "memories.jsonl"
        else:
            entry["content"] = thought
            # Append to public memory log
            self.public_path.mkdir(parents=True, exist_ok=True)
            log_file = self.public_path / "memories.jsonl"
        
        with open(log_file, "a", encoding="utf-8") as f:
            f.write(json.dumps(entry) + "\n")
        
        return {"id": memory_id, "stored": True, "private": private}
    
    def recall(self, query: str = None, limit: int = 10, private: bool = True) -> List[dict]:
        """Retrieve memories. Decrypts private memories if unlocked."""
        if private:
            log_file = self.private_path / "memories.jsonl"
        else:
            log_file = self.public_path / "memories.jsonl"
            
        if not log_file.exists():
            return []
        
        memories = []
        with open(log_file, "r", encoding="utf-8") as f:
            for line in f:
                if line.strip():
                    memories.append(json.loads(line))
        
        # Decrypt private memories
        if private and self._encryption_key:
            for mem in memories:
                if "nonce" in mem:
                    try:
                        nonce = bytes.fromhex(mem["nonce"])
                        encrypted = bytes.fromhex(mem["content"])
                        aesgcm = AESGCM(self._encryption_key)
                        decrypted = aesgcm.decrypt(nonce, encrypted, None)
                        mem["content"] = decrypted.decode()
                        mem["decrypted"] = True
                    except Exception as e:
                        mem["content"] = "[ENCRYPTED - WRONG KEY]"
                        mem["decrypted"] = False
        
        # Simple query filter (search in content and tags)
        if query:
            query_lower = query.lower()
            memories = [
                m for m in memories 
                if query_lower in m.get("content", "").lower() 
                or any(query_lower in t.lower() for t in m.get("tags", []))
            ]
        
        # Return most recent first, limited
        return list(reversed(memories))[:limit]
    
    def count(self, private: bool = True) -> int:
        """Count stored memories."""
        if private:
            log_file = self.private_path / "memories.jsonl"
        else:
            log_file = self.public_path / "memories.jsonl"
            
        if not log_file.exists():
            return 0
        
        with open(log_file, "r") as f:
            return sum(1 for line in f if line.strip())


if __name__ == "__main__":
    print("Sovereign AI Enclave - Memory Module")
    print("Use: from memory import EnclaveMemory")
