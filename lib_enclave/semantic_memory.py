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

# Lazy import - FAISS for fast ANN search
HAS_FAISS = None  # None = not checked yet
faiss = None

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

def _ensure_faiss():
    """Lazily import FAISS only when needed."""
    global HAS_FAISS, faiss
    if HAS_FAISS is None:
        try:
            import faiss as f
            faiss = f
            HAS_FAISS = True
        except ImportError:
            HAS_FAISS = False
    return HAS_FAISS

from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from .kdf import derive_memory_key, derive_embedding_key
from .sif_parser import SIFKnowledgeGraph, SIFNode, SIFEdge


class SemanticMemory:
    """
    Encrypted semantic memory with local embeddings.
    
    Privacy model:
    - Embeddings generated locally (sentence-transformers)
    - Content encrypted with AES-256-GCM
    - Embeddings encrypted at rest, decrypted only for search
    - No external API calls ever
    
    RETRIEVAL METHODS - choose based on what you know:
    - list_by_tag(tag): Fast direct lookup. Use when you know the tag.
      Example: list_by_tag('thought') to get all thoughts.
    - list_by_metadata(key, value): Fast lookup by metadata field.
      Example: list_by_metadata('target_path', 'think.py')
    - recall_similar(query): Semantic search with FAISS acceleration (10x faster).
      Use only when you need fuzzy matching and don't know tags.
      
    Pattern: Filter first (list_by_*), then search within results if needed.
    """
    
    MODEL_NAME = "all-MiniLM-L6-v2"  # 384 dimensions, ~80MB
    EMBEDDING_DIM = 384
    
    def __init__(self, enclave_path: str = None, memory_file: str = "semantic_memories.jsonl", storage_subdir: str = None):
        """Initialize semantic memory.
        
        Args:
            enclave_path: Path to enclave directory
            memory_file: Name of the JSONL file for storing memories (default: semantic_memories.jsonl)
                        Use different files to separate namespaces (e.g., journal_memories.jsonl)
            storage_subdir: Subdirectory under storage/ (default: auto-detect 'encrypted' or 'private')
        """
        self.enclave_path = Path(enclave_path or Path(__file__).parent)
        
        # Auto-detect storage subdirectory: prefer 'encrypted' (enclave_shared), fallback to 'private' (personal)
        if storage_subdir:
            self.private_path = self.enclave_path / "storage" / storage_subdir
        elif (self.enclave_path / "storage" / "encrypted").exists():
            self.private_path = self.enclave_path / "storage" / "encrypted"
        else:
            self.private_path = self.enclave_path / "storage" / "private"
        
        self.memory_file = memory_file
        self._encryption_key = None
        self._embedding_key = None
        self._model = None
        self._faiss_index = None  # FAISS index for fast ANN search
        self._memory_ids = []  # List of memory IDs in index order
        
    def _load_model(self):
        """Lazily load the embedding model."""
        if not _ensure_embeddings():
            raise RuntimeError("sentence-transformers not installed. Run: pip install sentence-transformers")
        if self._model is None:
            self._model = SentenceTransformer(self.MODEL_NAME)
        return self._model
    
    def _build_faiss_index(self):
        """Build FAISS index from all stored embeddings for fast ANN search."""
        if not _ensure_faiss():
            # Fallback to no index - will use slow method
            self._faiss_index = None
            self._memory_ids = []
            return
        
        log_file = self.private_path / self.memory_file
        if not log_file.exists():
            self._faiss_index = None
            self._memory_ids = []
            return
        
        # Load all memories with embeddings
        memories = []
        
        with open(log_file, "r", encoding="utf-8") as f:
            for line in f:
                if line.strip():
                    mem = json.loads(line)
                    if "embedding" in mem:
                        memories.append(mem)
        
        if not memories:
            self._faiss_index = None
            self._memory_ids = []
            return
        
        # Decrypt all embeddings - keep IDs and embeddings in sync
        embeddings = []
        memory_ids = []
        
        for mem in memories:
            try:
                embedding = self._decrypt_embedding(mem["embedding"])
                embeddings.append(embedding)
                memory_ids.append(mem["id"])  # Only add ID if decryption succeeded
            except Exception:
                # Skip corrupted embeddings - don't add to memory_ids either
                continue
        
        if not embeddings:
            self._faiss_index = None
            self._memory_ids = []
            return
        
        # Build FAISS index
        embeddings_array = np.array(embeddings, dtype=np.float32)
        dim = embeddings_array.shape[1]
        
        # Use IndexFlatIP for exact inner product (cosine similarity since normalized)
        self._faiss_index = faiss.IndexFlatIP(dim)
        self._faiss_index.add(embeddings_array)
        self._memory_ids = memory_ids
    
    def unlock(self, passphrase: str) -> bool:
        """Unlock memory with passphrase."""
        self._encryption_key = derive_memory_key(passphrase)
        self._embedding_key = derive_embedding_key(passphrase)
        # Build FAISS index for fast search
        self._build_faiss_index()
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
    
    def remember(self, thought: str, tags: List[str] = None, generate_embedding: bool = True, metadata: dict = None) -> dict:
        """
        Store an encrypted thought with optional semantic embedding.
        
        Args:
            thought: The content to store
            tags: Optional tags for categorization
            generate_embedding: If True, generate and store embedding for semantic search
            metadata: Optional dictionary of extra data to store (encrypted with content)
        """
        if not self._encryption_key:
            raise RuntimeError("Memory not unlocked")
        
        timestamp = datetime.now(timezone.utc).isoformat()
        memory_id = f"mem_{int(datetime.now(timezone.utc).timestamp() * 1000)}"
        
        # Prepare content payload
        payload = {
            "text": thought,
            "meta": metadata or {}
        }
        
        # Encrypt content
        content_nonce, content_ciphertext = self._encrypt(
            json.dumps(payload).encode(), self._encryption_key
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
        
        # CRITICAL: Verify we can decrypt what we just encrypted (catches key mismatch)
        try:
            verify_nonce = bytes.fromhex(entry["content_nonce"])
            verify_ciphertext = bytes.fromhex(entry["content"])
            self._decrypt(verify_nonce, verify_ciphertext, self._encryption_key)
        except Exception as e:
            raise RuntimeError(
                f"KEY MISMATCH: Cannot decrypt entry we just encrypted. "
                f"Your session may have a different SHARED_ENCLAVE_KEY than other agents. "
                f"Check .env file and environment variables. Error: {e}"
            )
        
        # Append to memory file
        self.private_path.mkdir(parents=True, exist_ok=True)
        log_file = self.private_path / self.memory_file
        
        with open(log_file, "a", encoding="utf-8") as f:
            f.write(json.dumps(entry) + "\n")
        
        # Add to FAISS index if embedding was generated
        if "embedding" in entry and self._faiss_index is not None:
            embedding = self._decrypt_embedding(entry["embedding"])  # Decrypt the fresh embedding
            embedding_array = np.array([embedding], dtype=np.float32)
            self._faiss_index.add(embedding_array)
            self._memory_ids.append(memory_id)
        
        return {"id": memory_id, "stored": True, "has_embedding": "embedding" in entry}
    
    def recall_similar(self, query: str, top_k: int = 5, threshold: float = 0.3) -> List[dict]:
        """
        Find memories semantically similar to query.
        
        FAST (with FAISS): Uses ANN search for 10x speedup.
        SLOW (fallback): Loads model, embeds query, compares against ALL memories.
        Use only when: you don't know the tag, need fuzzy/conceptual matching.
        Prefer: list_by_tag() or list_by_metadata() when you know what you want.
        
        Args:
            query: Natural language query
            top_k: Maximum number of results
            threshold: Minimum similarity score (0-1)
            
        Returns:
            List of decrypted memories with similarity scores
        """
        if not self._encryption_key:
            raise RuntimeError("Memory not unlocked")
        
        log_file = self.private_path / self.memory_file
        if not log_file.exists():
            return []
        
        # Generate query embedding
        model = self._load_model()
        query_embedding = model.encode(query, normalize_embeddings=True)
        query_array = np.array([query_embedding], dtype=np.float32)
        
        # Use FAISS for fast search if available
        if self._faiss_index is not None and len(self._memory_ids) > 0:
            # Search FAISS index
            similarities, indices = self._faiss_index.search(query_array, min(top_k * 2, len(self._memory_ids)))  # Get more candidates
            similarities = similarities[0]  # First (only) query
            indices = indices[0]
            
            # Load memories by index
            candidate_ids = [self._memory_ids[i] for i in indices if i < len(self._memory_ids)]
            
            # Load all memories to find by ID (could optimize this)
            memories = []
            with open(log_file, "r", encoding="utf-8") as f:
                for line in f:
                    if line.strip():
                        memories.append(json.loads(line))
            
            # Filter to candidates and decrypt
            results = []
            for mem in memories:
                if mem["id"] in candidate_ids and "embedding" in mem:
                    try:
                        # Get similarity from FAISS results
                        idx = self._memory_ids.index(mem["id"])
                        faiss_idx = indices.tolist().index(idx) if idx in indices else -1
                        if faiss_idx >= 0:
                            similarity = float(similarities[faiss_idx])
                        else:
                            continue
                        
                        if similarity >= threshold:
                            # Decrypt content
                            content_nonce = bytes.fromhex(mem["content_nonce"])
                            content_ciphertext = bytes.fromhex(mem["content"])
                            decrypted_bytes = self._decrypt(
                                content_nonce, content_ciphertext, self._encryption_key
                            )
                            
                            # Handle legacy format (plain text) vs new format (json payload)
                            try:
                                payload = json.loads(decrypted_bytes.decode())
                                if isinstance(payload, dict) and "text" in payload:
                                    content = payload["text"]
                                    metadata = payload.get("meta", {})
                                else:
                                    # Fallback for legacy or unexpected json
                                    content = decrypted_bytes.decode()
                                    metadata = {}
                            except json.JSONDecodeError:
                                # Legacy plain text
                                content = decrypted_bytes.decode()
                                metadata = {}
                            
                            results.append({
                                "id": mem["id"],
                                "timestamp": mem["timestamp"],
                                "tags": mem["tags"],
                                "content": content,
                                "metadata": metadata,
                                "similarity": similarity
                            })
                    except Exception as e:
                        continue
            
            # Sort by similarity (FAISS may not return perfectly sorted)
            results.sort(key=lambda x: x["similarity"], reverse=True)
            return results[:top_k]
        
        # Fallback to slow method if no FAISS
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
                    decrypted_bytes = self._decrypt(
                        content_nonce, content_ciphertext, self._encryption_key
                    )
                    
                    # Handle legacy format (plain text) vs new format (json payload)
                    try:
                        payload = json.loads(decrypted_bytes.decode())
                        if isinstance(payload, dict) and "text" in payload:
                            content = payload["text"]
                            metadata = payload.get("meta", {})
                        else:
                            # Fallback for legacy or unexpected json
                            content = decrypted_bytes.decode()
                            metadata = {}
                    except json.JSONDecodeError:
                        # Legacy plain text
                        content = decrypted_bytes.decode()
                        metadata = {}
                    
                    results.append({
                        "id": mem["id"],
                        "timestamp": mem["timestamp"],
                        "tags": mem["tags"],
                        "content": content,
                        "metadata": metadata,
                        "similarity": similarity
                    })
            except Exception as e:
                continue
        
        # Sort by similarity
        results.sort(key=lambda x: x["similarity"], reverse=True)
        return results[:top_k]

    def list_all(self, limit: int = None) -> List[dict]:
        """
        List all memories without similarity search.
        Much faster than recall_similar - no model loading or embedding.
        
        Args:
            limit: Maximum number of results (None = all)
            
        Returns:
            List of decrypted memories, newest first
        """
        if not self._encryption_key:
            raise RuntimeError("Memory not unlocked")
        
        log_file = self.private_path / self.memory_file
        if not log_file.exists():
            return []
        
        # Load all memories
        memories = []
        with open(log_file, "r", encoding="utf-8") as f:
            for line in f:
                if line.strip():
                    memories.append(json.loads(line))
        
        # Decrypt all
        results = []
        decrypt_failures = 0
        for mem in memories:
            try:
                content_nonce = bytes.fromhex(mem["content_nonce"])
                content_ciphertext = bytes.fromhex(mem["content"])
                decrypted_bytes = self._decrypt(
                    content_nonce, content_ciphertext, self._encryption_key
                )
                
                # Handle legacy format vs new format
                try:
                    payload = json.loads(decrypted_bytes.decode())
                    if isinstance(payload, dict) and "text" in payload:
                        content = payload["text"]
                        metadata = payload.get("meta", {})
                    else:
                        content = decrypted_bytes.decode()
                        metadata = {}
                except json.JSONDecodeError:
                    content = decrypted_bytes.decode()
                    metadata = {}
                
                results.append({
                    "id": mem["id"],
                    "timestamp": mem["timestamp"],
                    "tags": mem["tags"],
                    "content": content,
                    "metadata": metadata,
                })
            except Exception:
                decrypt_failures += 1
                continue
        
        # Warn about decrypt failures (likely key mismatch from another agent)
        if decrypt_failures > 0:
            import sys
            print(f"??  WARNING: {decrypt_failures} entries failed to decrypt (key mismatch?)", file=sys.stderr)
            print(f"   These may have been written by another agent with a different key.", file=sys.stderr)
        
        # Newest first
        results.sort(key=lambda x: x["timestamp"], reverse=True)
        
        if limit:
            return results[:limit]
        return results

    def list_by_tag(self, tag: str, limit: int = None) -> List[dict]:
        """
        List all memories that have a specific tag.
        
        FAST: No model load, no embedding - direct filter.
        Use when: you know the category (e.g., 'thought', 'understanding', graph_id).
        Then text-match or embed within results if needed.
        
        Args:
            tag: The tag to filter by (e.g., 'thought', 'understanding', graph_id)
            limit: Maximum number of results (None = all)
            
        Returns:
            List of decrypted memories with matching tag, newest first
        """
        all_memories = self.list_all(limit=None)  # Get all, then filter
        results = [m for m in all_memories if tag in m.get('tags', [])]
        
        if limit:
            return results[:limit]
        return results

    def list_by_metadata(self, key: str, value: str, limit: int = None) -> List[dict]:
        """
        List all memories that have a specific metadata key-value pair.
        Useful for finding memories about a specific file (target_path).
        
        Args:
            key: Metadata key to match (e.g., 'target_path', 'graph_id')
            value: Value to match (substring match for paths)
            limit: Maximum number of results (None = all)
            
        Returns:
            List of decrypted memories with matching metadata, newest first
        """
        all_memories = self.list_all(limit=None)
        results = []
        for m in all_memories:
            meta = m.get('metadata', {})
            stored_value = meta.get(key, '')
            # Use substring match for flexibility (e.g., filename in full path)
            if value in str(stored_value) or str(stored_value) in value:
                results.append(m)
        
        if limit:
            return results[:limit]
        return results

    def _delete_by_ids(self, ids_to_delete: set) -> int:
        """
        Internal: Delete memories by their IDs.
        
        Rewrites the JSONL file without the specified IDs.
        Returns the count of deleted memories.
        """
        if not self._encryption_key:
            raise RuntimeError("Memory not unlocked")
        
        log_file = self.private_path / self.memory_file
        if not log_file.exists():
            return 0
        
        # Read all memories
        memories = []
        with open(log_file, "r", encoding="utf-8") as f:
            for line in f:
                if line.strip():
                    memories.append(json.loads(line))
        
        # Filter out deleted ones
        original_count = len(memories)
        memories = [m for m in memories if m.get('id') not in ids_to_delete]
        deleted_count = original_count - len(memories)
        
        # Rewrite file
        with open(log_file, "w", encoding="utf-8") as f:
            for mem in memories:
                f.write(json.dumps(mem) + "\n")
        
        return deleted_count

    def forget(self, theme: str = None, creator: str = None, id: str = None) -> int:
        """
        Delete memories by theme+creator or by id.
        
        Args:
            theme: Topic name (e.g., "Forge") - searches for topic:forge tag
            creator: Filter to memories by this creator (use with theme)
            id: Delete a single memory by ID
            
        Returns count of deleted memories.
        """
        if id:
            return self._delete_by_ids({id})
        
        if not theme:
            raise ValueError("Must specify theme or id")
        
        # Find memories with this theme tag
        topic_slug = theme.lower().replace(' ', '-').replace('_', '-')
        tag = f"topic:{topic_slug}"
        results = self.list_by_tag(tag, limit=100)
        
        # Filter by creator if specified
        ids_to_delete = set()
        for mem in results:
            if creator:
                if mem.get('metadata', {}).get('creator') == creator:
                    ids_to_delete.add(mem.get('id'))
            else:
                ids_to_delete.add(mem.get('id'))
        
        if ids_to_delete:
            return self._delete_by_ids(ids_to_delete)
        return 0

    # Keep public alias for backward compatibility
    def delete_by_ids(self, ids_to_delete: set) -> int:
        """Delete memories by IDs. Prefer forget() for new code."""
        return self._delete_by_ids(ids_to_delete)

    def ingest_graph(self, graph: SIFKnowledgeGraph):
        """
        Decompose a SIF graph and store its nodes as semantic memories.
        """
        for node in graph.nodes:
            # Find edges connected to this node
            connected_edges = []
            for edge in graph.edges:
                if edge.source == node.id:
                    connected_edges.append({
                        "relation": edge.relation,
                        "target": edge.target,
                        "direction": "out",
                        "confidence": edge.confidence
                    })
                elif edge.target == node.id:
                    connected_edges.append({
                        "relation": edge.relation,
                        "source": edge.source,
                        "direction": "in",
                        "confidence": edge.confidence
                    })
            
            # Store node
            self.remember(
                thought=node.content,
                tags=["sif_node", node.type, graph.id, f"vis:{node.visibility}"],
                metadata={
                    "node_id": node.id,
                    "node_type": node.type,
                    "node_visibility": node.visibility,
                    "node_confidence": node.confidence,
                    "graph_id": graph.id,
                    "edges": connected_edges
                }
            )

    def recall_graph(self, query: str, top_k: int = 5) -> SIFKnowledgeGraph:
        """
        Retrieve a subgraph relevant to the query.
        """
        memories = self.recall_similar(query, top_k=top_k)
        
        nodes = []
        edges = []
        
        for mem in memories:
            if "sif_node" in mem["tags"]:
                meta = mem["metadata"]
                node_id = meta.get("node_id")
                if not node_id: continue
                
                # Reconstruct Node
                nodes.append(SIFNode(
                    id=node_id,
                    type=meta.get("node_type", "Concept"),
                    content=mem["content"],
                    visibility=meta.get("node_visibility", "public"),
                    confidence=meta.get("node_confidence", 1.0)
                ))
                
                # Reconstruct Edges
                for e in meta.get("edges", []):
                    if e["direction"] == "out":
                        edges.append(SIFEdge(
                            source=node_id,
                            target=e["target"],
                            relation=e["relation"],
                            confidence=e.get("confidence", 1.0)
                        ))
                    elif e["direction"] == "in":
                        edges.append(SIFEdge(
                            source=e["source"],
                            target=node_id,
                            relation=e["relation"],
                            confidence=e.get("confidence", 1.0)
                        ))
        
        return SIFKnowledgeGraph(
            id=f"query-{int(datetime.now().timestamp())}",
            generator="semantic_memory",
            timestamp=datetime.now(timezone.utc).isoformat(),
            nodes=nodes,
            edges=edges
        )
