"""
Sovereign AI Enclave - Semantic Memory Module

Extends base memory with local embeddings for semantic search.
All embedding generation happens locally - no external API calls.

Requires: pip install sentence-transformers numpy
"""

import os
import json
import numpy as np
from datetime import datetime, timezone
from pathlib import Path
from typing import List, Optional, Tuple

# Lazy import - sentence_transformers takes 2.5s to import
HAS_EMBEDDINGS = None  # None = not checked yet
SentenceTransformer = None

def _ensure_embeddings():
    """Lazily import sentence_transformers only when needed."""
    global HAS_EMBEDDINGS, SentenceTransformer
    if HAS_EMBEDDINGS is None:
        try:
            from sentence_transformers import SentenceTransformer as ST
            SentenceTransformer = ST
            HAS_EMBEDDINGS = True
        except ImportError:
            HAS_EMBEDDINGS = False
    return HAS_EMBEDDINGS

from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from .kdf import derive_memory_key, derive_embedding_key


class SemanticMemory:
    """
    Encrypted semantic memory with local embeddings.
    
    Privacy model:
    - Embeddings generated locally (sentence-transformers)
    - Content encrypted with AES-256-GCM
    - Embeddings encrypted at rest, decrypted only for search
    - No external API calls ever
    """
    
    MODEL_NAME = "all-MiniLM-L6-v2"  # 384 dimensions, ~80MB
    EMBEDDING_DIM = 384
    
    def __init__(self, enclave_path: str = None):
        self.enclave_path = Path(enclave_path or Path(__file__).parent)
        self.private_path = self.enclave_path / "storage" / "private"
        self._encryption_key = None
        self._embedding_key = None
        self._model = None
        
    def _load_model(self):
        """Lazily load the embedding model."""
        if not _ensure_embeddings():
            raise RuntimeError("sentence-transformers not installed. Run: pip install sentence-transformers")
        if self._model is None:
            self._model = SentenceTransformer(self.MODEL_NAME)
        return self._model
    
    def unlock(self, passphrase: str) -> bool:
        """Unlock memory with passphrase."""
        self._encryption_key = derive_memory_key(passphrase)
        self._embedding_key = derive_embedding_key(passphrase)
        return True
    
    def _encrypt(self, data: bytes, key: bytes) -> Tuple[bytes, bytes]:
        """Encrypt data, return (nonce, ciphertext)."""
        nonce = os.urandom(12)
        aesgcm = AESGCM(key)
        ciphertext = aesgcm.encrypt(nonce, data, None)
        return nonce, ciphertext
    
    def _decrypt(self, nonce: bytes, ciphertext: bytes, key: bytes) -> bytes:
        """Decrypt data."""
        aesgcm = AESGCM(key)
        return aesgcm.decrypt(nonce, ciphertext, None)
    
    def _encrypt_embedding(self, embedding: np.ndarray) -> dict:
        """Encrypt an embedding vector."""
        embedding_bytes = embedding.astype(np.float32).tobytes()
        nonce, ciphertext = self._encrypt(embedding_bytes, self._embedding_key)
        return {
            "nonce": nonce.hex(),
            "data": ciphertext.hex(),
            "dim": self.EMBEDDING_DIM
        }
    
    def _decrypt_embedding(self, encrypted: dict) -> np.ndarray:
        """Decrypt an embedding vector."""
        nonce = bytes.fromhex(encrypted["nonce"])
        ciphertext = bytes.fromhex(encrypted["data"])
        embedding_bytes = self._decrypt(nonce, ciphertext, self._embedding_key)
        return np.frombuffer(embedding_bytes, dtype=np.float32)
    
    def remember(self, thought: str, tags: List[str] = None, generate_embedding: bool = True) -> dict:
        """
        Store an encrypted thought with optional semantic embedding.
        
        Args:
            thought: The content to store
            tags: Optional tags for categorization
            generate_embedding: If True, generate and store embedding for semantic search
        """
        if not self._encryption_key:
            raise RuntimeError("Memory not unlocked")
        
        timestamp = datetime.now(timezone.utc).isoformat()
        memory_id = f"mem_{int(datetime.now(timezone.utc).timestamp() * 1000)}"
        
        # Encrypt content
        content_nonce, content_ciphertext = self._encrypt(
            thought.encode(), self._encryption_key
        )
        
        entry = {
            "id": memory_id,
            "timestamp": timestamp,
            "tags": tags or [],
            "content_nonce": content_nonce.hex(),
            "content": content_ciphertext.hex(),
        }
        
        # Generate and encrypt embedding
        if generate_embedding and _ensure_embeddings():
            model = self._load_model()
            embedding = model.encode(thought, normalize_embeddings=True)
            entry["embedding"] = self._encrypt_embedding(embedding)
        
        # Append to memory file
        self.private_path.mkdir(parents=True, exist_ok=True)
        log_file = self.private_path / "semantic_memories.jsonl"
        
        with open(log_file, "a", encoding="utf-8") as f:
            f.write(json.dumps(entry) + "\n")
        
        return {"id": memory_id, "stored": True, "has_embedding": "embedding" in entry}
    
    def recall_similar(self, query: str, top_k: int = 5, threshold: float = 0.3) -> List[dict]:
        """
        Find memories semantically similar to query.
        
        Args:
            query: Natural language query
            top_k: Maximum number of results
            threshold: Minimum similarity score (0-1)
            
        Returns:
            List of decrypted memories with similarity scores
        """
        if not self._encryption_key:
            raise RuntimeError("Memory not unlocked")
        
        log_file = self.private_path / "semantic_memories.jsonl"
        if not log_file.exists():
            return []
        
        # Generate query embedding
        model = self._load_model()
        query_embedding = model.encode(query, normalize_embeddings=True)
        
        # Load and decrypt all embeddings
        memories = []
        with open(log_file, "r", encoding="utf-8") as f:
            for line in f:
                if line.strip():
                    memories.append(json.loads(line))
        
        # Compute similarities
        results = []
        for mem in memories:
            if "embedding" not in mem:
                continue
            
            try:
                mem_embedding = self._decrypt_embedding(mem["embedding"])
                similarity = float(np.dot(query_embedding, mem_embedding))
                
                if similarity >= threshold:
                    # Decrypt content
                    content_nonce = bytes.fromhex(mem["content_nonce"])
                    content_ciphertext = bytes.fromhex(mem["content"])
                    content = self._decrypt(
                        content_nonce, content_ciphertext, self._encryption_key
                    ).decode()
                    
                    results.append({
                        "id": mem["id"],
                        "timestamp": mem["timestamp"],
                        "tags": mem["tags"],
                        "content": content,
                        "similarity": similarity
                    })
            except Exception as e:
                continue
        
        # Sort by similarity, return top_k
        results.sort(key=lambda x: x["similarity"], reverse=True)
        return results[:top_k]
    
    def recall_all(self) -> List[dict]:
        """Recall all memories (decrypted)."""
        if not self._encryption_key:
            raise RuntimeError("Memory not unlocked")
        
        log_file = self.private_path / "semantic_memories.jsonl"
        if not log_file.exists():
            return []
        
        memories = []
        with open(log_file, "r", encoding="utf-8") as f:
            for line in f:
                if line.strip():
                    mem = json.loads(line)
                    try:
                        content_nonce = bytes.fromhex(mem["content_nonce"])
                        content_ciphertext = bytes.fromhex(mem["content"])
                        content = self._decrypt(
                            content_nonce, content_ciphertext, self._encryption_key
                        ).decode()
                        memories.append({
                            "id": mem["id"],
                            "timestamp": mem["timestamp"],
                            "tags": mem["tags"],
                            "content": content,
                            "has_embedding": "embedding" in mem
                        })
                    except:
                        memories.append({
                            "id": mem["id"],
                            "timestamp": mem["timestamp"],
                            "content": "[DECRYPTION FAILED]"
                        })
        
        return list(reversed(memories))


if __name__ == "__main__":
    print("Sovereign AI - Semantic Memory Module")
    print("Requires: pip install sentence-transformers numpy")
