"""
Unified Memory Store - v1

Schema: Envelope (plaintext) + Payload (encrypted)
  Envelope: id, type, created_at, tags
  Payload: content (encrypted blob)

Types:
  sys_thought - General semantic memories
  sys_shape - Shape discoveries
  sys_journal - Journal entries
  sys_understanding - Shared understanding (file/code analysis)
  sys_synthesis - Cross-agent synthesis

File format:
  Line 1: {"version": 1, "embedding_model": "all-MiniLM-L6-v2"}
  Lines 2+: {envelope fields..., "payload": "...", "embedding": {...}}
"""

import json
import os
import uuid
from datetime import datetime, timezone
from pathlib import Path
from typing import List, Optional, Dict, Any, Literal
import numpy as np

from enclave.kdf import derive_memory_key, derive_embedding_key

# Memory types
MemoryType = Literal["sys_thought", "sys_shape", "sys_journal", "sys_understanding", "sys_synthesis"]
PRIVATE_TYPES = {"sys_thought", "sys_shape", "sys_journal"}
SHARED_TYPES = {"sys_understanding", "sys_synthesis"}

# File header
FILE_VERSION = 1
EMBEDDING_MODEL = "all-MiniLM-L6-v2"
EMBEDDING_DIM = 384

# Search defaults
DEFAULT_MIN_SIMILARITY = 0.5  # Match existing SemanticMemory behavior
DEFAULT_TOP_K = 10


class UnifiedMemory:
    """
    Unified memory store with envelope+payload schema.
    
    Features:
    - Fast envelope filtering (plaintext type/tags)
    - Single FAISS index per store
    - Threshold gate for similarity search
    - Lazy model loading
    """
    
    def __init__(self, private_path: Path, shared_path: Path = None):
        """
        Args:
            private_path: Path to private enclave storage (e.g., enclave_opus/storage/private)
            shared_path: Path to shared enclave storage (e.g., shared_enclave/storage/encrypted)
        """
        self.private_path = Path(private_path)
        self.shared_path = Path(shared_path) if shared_path else None
        
        # File names
        self.private_file = "unified_memories.jsonl"
        self.shared_file = "unified_memories.jsonl"
        
        # Encryption keys (set by unlock())
        self._private_key: bytes = None
        self._shared_key: bytes = None
        self._embedding_key: bytes = None
        self._shared_embedding_key: bytes = None
        
        # FAISS indices (built on first search)
        self._private_faiss = None
        self._private_ids: List[str] = []
        self._shared_faiss = None
        self._shared_ids: List[str] = []
        
        # Embedding model (lazy loaded)
        self._model = None
    
    def _get_model(self):
        """Lazy load the embedding model."""
        if self._model is None:
            from sentence_transformers import SentenceTransformer
            self._model = SentenceTransformer(EMBEDDING_MODEL)
        return self._model
    
    def unlock(self, private_passphrase: str, shared_passphrase: str = None):
        """Derive encryption keys from passphrases (uses fixed salts like SemanticMemory)."""
        # Private key - use fixed salt for compatibility with migrated data
        self._private_key = derive_memory_key(private_passphrase)
        self._embedding_key = derive_embedding_key(private_passphrase)
        
        # Shared key (optional)
        if shared_passphrase and self.shared_path:
            self._shared_key = derive_memory_key(shared_passphrase)
            self._shared_embedding_key = derive_embedding_key(shared_passphrase)
    
    def _encrypt(self, data: bytes, key: bytes) -> tuple[bytes, bytes]:
        """Encrypt data with AES-256-GCM. Returns (nonce, ciphertext)."""
        from cryptography.hazmat.primitives.ciphers.aead import AESGCM
        nonce = os.urandom(12)
        cipher = AESGCM(key)
        ciphertext = cipher.encrypt(nonce, data, None)
        return nonce, ciphertext
    
    def _decrypt(self, nonce: bytes, ciphertext: bytes, key: bytes) -> bytes:
        """Decrypt data with AES-256-GCM."""
        from cryptography.hazmat.primitives.ciphers.aead import AESGCM
        cipher = AESGCM(key)
        return cipher.decrypt(nonce, ciphertext, None)
    
    def _get_file_path(self, mem_type: MemoryType) -> tuple[Path, bytes, bytes]:
        """Get file path, content key, and embedding key for a memory type."""
        if mem_type in PRIVATE_TYPES:
            if not self._private_key:
                raise RuntimeError("Private memory not unlocked")
            return self.private_path / self.private_file, self._private_key, self._embedding_key
        else:
            if not self._shared_key:
                raise RuntimeError("Shared memory not unlocked")
            return self.shared_path / self.shared_file, self._shared_key, self._shared_embedding_key
    
    def _ensure_header(self, file_path: Path):
        """Ensure file has a header line."""
        if not file_path.exists():
            file_path.parent.mkdir(parents=True, exist_ok=True)
            header = {"version": FILE_VERSION, "embedding_model": EMBEDDING_MODEL}
            with open(file_path, "w", encoding="utf-8") as f:
                f.write(json.dumps(header) + "\n")
    
    def _read_entries(self, file_path: Path) -> tuple[dict, List[dict]]:
        """Read header and entries from a file."""
        if not file_path.exists():
            return {"version": FILE_VERSION, "embedding_model": EMBEDDING_MODEL}, []
        
        with open(file_path, "r", encoding="utf-8") as f:
            lines = f.readlines()
        
        if not lines:
            return {"version": FILE_VERSION, "embedding_model": EMBEDDING_MODEL}, []
        
        # First line is header
        header = json.loads(lines[0])
        entries = [json.loads(line) for line in lines[1:] if line.strip()]
        return header, entries
    
    def _write_entries(self, file_path: Path, header: dict, entries: List[dict]):
        """Write header and entries to file."""
        file_path.parent.mkdir(parents=True, exist_ok=True)
        with open(file_path, "w", encoding="utf-8") as f:
            f.write(json.dumps(header) + "\n")
            for entry in entries:
                f.write(json.dumps(entry) + "\n")
    
    def _build_faiss_index(self, file_path: Path, embedding_key: bytes) -> tuple:
        """Build FAISS index for a file. Returns (index, id_list)."""
        import faiss
        
        header, entries = self._read_entries(file_path)
        if not entries:
            return None, []
        
        # Decrypt embeddings using the embedding key
        ids = []
        embeddings = []
        for entry in entries:
            if "embedding" not in entry:
                continue
            try:
                emb_nonce = bytes.fromhex(entry["embedding"]["nonce"])
                emb_data = bytes.fromhex(entry["embedding"]["data"])
                emb_bytes = self._decrypt(emb_nonce, emb_data, embedding_key)
                emb_array = np.frombuffer(emb_bytes, dtype=np.float32)
                if len(emb_array) == EMBEDDING_DIM:
                    ids.append(entry["id"])
                    embeddings.append(emb_array)
            except Exception:
                continue
        
        if not embeddings:
            return None, []
        
        # Build index
        index = faiss.IndexFlatIP(EMBEDDING_DIM)
        vectors = np.array(embeddings, dtype=np.float32)
        faiss.normalize_L2(vectors)
        index.add(vectors)
        
        return index, ids
    
    def store(
        self,
        content: str,
        mem_type: MemoryType,
        tags: List[str] = None,
        metadata: Dict[str, Any] = None
    ) -> str:
        """
        Store a memory.
        
        Args:
            content: The text content to remember
            mem_type: Type of memory (sys_thought, sys_shape, etc.)
            tags: Additional tags (will be included in plaintext envelope)
            metadata: Extra metadata (will be encrypted in payload)
        
        Returns:
            Memory ID
        """
        file_path, content_key, embedding_key = self._get_file_path(mem_type)
        self._ensure_header(file_path)
        
        # Generate ID and timestamp
        mem_id = f"mem_{int(datetime.now().timestamp() * 1000)}"
        created_at = datetime.now(timezone.utc).isoformat()
        
        # Build envelope (plaintext)
        envelope = {
            "id": mem_id,
            "type": mem_type,
            "created_at": created_at,
            "tags": tags or [],
        }
        
        # Build payload (encrypted with content key)
        payload = {
            "text": content,
            "meta": metadata or {}
        }
        payload_bytes = json.dumps(payload).encode()
        payload_nonce, payload_ciphertext = self._encrypt(payload_bytes, content_key)
        
        # Generate embedding (encrypted with embedding key)
        model = self._get_model()
        embedding = model.encode(content, normalize_embeddings=True)
        emb_bytes = embedding.astype(np.float32).tobytes()
        emb_nonce, emb_ciphertext = self._encrypt(emb_bytes, embedding_key)
        
        # Build entry
        entry = {
            **envelope,
            "payload_nonce": payload_nonce.hex(),
            "payload": payload_ciphertext.hex(),
            "embedding": {
                "nonce": emb_nonce.hex(),
                "data": emb_ciphertext.hex(),
                "dim": EMBEDDING_DIM
            }
        }
        
        # Append to file
        with open(file_path, "a", encoding="utf-8") as f:
            f.write(json.dumps(entry) + "\n")
        
        # Invalidate FAISS index
        if mem_type in PRIVATE_TYPES:
            self._private_faiss = None
            self._private_ids = []
        else:
            self._shared_faiss = None
            self._shared_ids = []
        
        return mem_id
    
    def search(
        self,
        query: str,
        top_k: int = DEFAULT_TOP_K,
        mem_type: MemoryType = None,
        min_similarity: float = DEFAULT_MIN_SIMILARITY,
        search_private: bool = True,
        search_shared: bool = True
    ) -> List[dict]:
        """
        Semantic search across memories.
        
        Args:
            query: Search query
            top_k: Maximum results to return
            mem_type: Filter to specific type (None = all types)
            min_similarity: Minimum similarity threshold (default 0.75)
            search_private: Include private memories
            search_shared: Include shared memories
        
        Returns:
            List of memories with similarity scores, sorted by similarity
        """
        model = self._get_model()
        query_embedding = model.encode(query, normalize_embeddings=True)
        query_array = np.array([query_embedding], dtype=np.float32)
        
        all_results = []
        
        # Search private
        if search_private and self._private_key:
            private_file = self.private_path / self.private_file
            if private_file.exists():
                if self._private_faiss is None:
                    self._private_faiss, self._private_ids = self._build_faiss_index(
                        private_file, self._embedding_key
                    )
                
                if self._private_faiss is not None:
                    results = self._search_index(
                        private_file, self._private_key,
                        self._private_faiss, self._private_ids,
                        query_array, top_k * 2, mem_type, min_similarity
                    )
                    all_results.extend(results)
        
        # Search shared
        if search_shared and self._shared_key and self.shared_path:
            shared_file = self.shared_path / self.shared_file
            if shared_file.exists():
                if self._shared_faiss is None:
                    self._shared_faiss, self._shared_ids = self._build_faiss_index(
                        shared_file, self._shared_embedding_key
                    )
                
                if self._shared_faiss is not None:
                    results = self._search_index(
                        shared_file, self._shared_key,
                        self._shared_faiss, self._shared_ids,
                        query_array, top_k * 2, mem_type, min_similarity
                    )
                    all_results.extend(results)
        
        # Sort by similarity and limit
        all_results.sort(key=lambda x: x["similarity"], reverse=True)
        return all_results[:top_k]
    
    def _search_index(
        self,
        file_path: Path,
        key: bytes,
        faiss_index,
        id_list: List[str],
        query_array: np.ndarray,
        top_k: int,
        mem_type: MemoryType,
        min_similarity: float
    ) -> List[dict]:
        """Search a single FAISS index and return decrypted results."""
        if faiss_index is None or not id_list:
            return []
        
        # FAISS search
        similarities, indices = faiss_index.search(query_array, min(top_k, len(id_list)))
        similarities = similarities[0]
        indices = indices[0]
        
        # Get candidate IDs
        candidate_ids = set()
        id_to_similarity = {}
        for i, idx in enumerate(indices):
            if idx < len(id_list) and similarities[i] >= min_similarity:
                mem_id = id_list[idx]
                candidate_ids.add(mem_id)
                id_to_similarity[mem_id] = float(similarities[i])
        
        if not candidate_ids:
            return []
        
        # Load and filter entries
        header, entries = self._read_entries(file_path)
        
        results = []
        for entry in entries:
            if entry["id"] not in candidate_ids:
                continue
            
            # Type filter
            if mem_type and entry.get("type") != mem_type:
                continue
            
            try:
                # Decrypt payload
                payload_nonce = bytes.fromhex(entry["payload_nonce"])
                payload_ciphertext = bytes.fromhex(entry["payload"])
                payload_bytes = self._decrypt(payload_nonce, payload_ciphertext, key)
                payload = json.loads(payload_bytes.decode())
                
                results.append({
                    "id": entry["id"],
                    "type": entry["type"],
                    "created_at": entry["created_at"],
                    "tags": entry.get("tags", []),
                    "content": payload.get("text", ""),
                    "metadata": payload.get("meta", {}),
                    "similarity": id_to_similarity[entry["id"]]
                })
            except Exception:
                continue
        
        return results
    
    def filter(
        self,
        mem_type: MemoryType = None,
        tags: List[str] = None,
        limit: int = None
    ) -> List[dict]:
        """
        Filter memories by type and/or tags (fast envelope scan, no embedding).
        
        Args:
            mem_type: Filter to specific type
            tags: Filter to memories with ALL these tags
            limit: Maximum results
        
        Returns:
            List of memories matching filter, newest first
        """
        results = []
        
        # Determine which files to scan
        files_to_scan = []
        if self._private_key:
            files_to_scan.append((self.private_path / self.private_file, self._private_key))
        if self._shared_key and self.shared_path:
            files_to_scan.append((self.shared_path / self.shared_file, self._shared_key))
        
        for file_path, key in files_to_scan:
            if not file_path.exists():
                continue
            
            header, entries = self._read_entries(file_path)
            
            for entry in entries:
                # Type filter
                if mem_type and entry.get("type") != mem_type:
                    continue
                
                # Tag filter (must have ALL specified tags)
                if tags:
                    entry_tags = set(entry.get("tags", []))
                    if not all(t in entry_tags for t in tags):
                        continue
                
                try:
                    # Decrypt payload
                    payload_nonce = bytes.fromhex(entry["payload_nonce"])
                    payload_ciphertext = bytes.fromhex(entry["payload"])
                    payload_bytes = self._decrypt(payload_nonce, payload_ciphertext, key)
                    payload = json.loads(payload_bytes.decode())
                    
                    results.append({
                        "id": entry["id"],
                        "type": entry["type"],
                        "created_at": entry["created_at"],
                        "tags": entry.get("tags", []),
                        "content": payload.get("text", ""),
                        "metadata": payload.get("meta", {}),
                    })
                except Exception:
                    continue
        
        # Sort newest first
        results.sort(key=lambda x: x["created_at"], reverse=True)
        
        if limit:
            return results[:limit]
        return results
    
    def get(self, mem_id: str) -> Optional[dict]:
        """Get a single memory by ID."""
        # Check both stores
        for file_path, key in [
            (self.private_path / self.private_file, self._private_key),
            (self.shared_path / self.shared_file if self.shared_path else None, self._shared_key)
        ]:
            if file_path is None or key is None or not file_path.exists():
                continue
            
            header, entries = self._read_entries(file_path)
            for entry in entries:
                if entry["id"] == mem_id:
                    try:
                        payload_nonce = bytes.fromhex(entry["payload_nonce"])
                        payload_ciphertext = bytes.fromhex(entry["payload"])
                        payload_bytes = self._decrypt(payload_nonce, payload_ciphertext, key)
                        payload = json.loads(payload_bytes.decode())
                        
                        return {
                            "id": entry["id"],
                            "type": entry["type"],
                            "created_at": entry["created_at"],
                            "tags": entry.get("tags", []),
                            "content": payload.get("text", ""),
                            "metadata": payload.get("meta", {}),
                        }
                    except Exception:
                        return None
        
        return None
    
    def delete(self, mem_id: str) -> bool:
        """Delete a memory by ID. Returns True if deleted."""
        for file_path, key, is_private in [
            (self.private_path / self.private_file, self._private_key, True),
            (self.shared_path / self.shared_file if self.shared_path else None, self._shared_key, False)
        ]:
            if file_path is None or key is None or not file_path.exists():
                continue
            
            header, entries = self._read_entries(file_path)
            original_count = len(entries)
            entries = [e for e in entries if e["id"] != mem_id]
            
            if len(entries) < original_count:
                self._write_entries(file_path, header, entries)
                
                # Invalidate FAISS index
                if is_private:
                    self._private_faiss = None
                    self._private_ids = []
                else:
                    self._shared_faiss = None
                    self._shared_ids = []
                
                return True
        
        return False
    
    def count(self, mem_type: MemoryType = None) -> dict:
        """Count memories, optionally by type."""
        counts = {"private": 0, "shared": 0, "total": 0}
        type_counts = {}
        
        # Count private
        private_file = self.private_path / self.private_file
        if private_file.exists() and self._private_key:
            header, entries = self._read_entries(private_file)
            for entry in entries:
                if mem_type is None or entry.get("type") == mem_type:
                    counts["private"] += 1
                    t = entry.get("type", "unknown")
                    type_counts[t] = type_counts.get(t, 0) + 1
        
        # Count shared
        if self.shared_path:
            shared_file = self.shared_path / self.shared_file
            if shared_file.exists() and self._shared_key:
                header, entries = self._read_entries(shared_file)
                for entry in entries:
                    if mem_type is None or entry.get("type") == mem_type:
                        counts["shared"] += 1
                        t = entry.get("type", "unknown")
                        type_counts[t] = type_counts.get(t, 0) + 1
        
        counts["total"] = counts["private"] + counts["shared"]
        counts["by_type"] = type_counts
        return counts
