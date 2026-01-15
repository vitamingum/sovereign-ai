"""
Sovereign AI Enclave

A secure execution environment for AI agents with:
- Cryptographic identity (Ed25519)
- Encrypted semantic memory (AES-256-GCM)
- Local embeddings for search
- Signed outputs for verification
"""

from .crypto import SovereignIdentity
from .semantic_memory import SemanticMemory
from .kdf import derive_key, derive_memory_key, derive_embedding_key, derive_directive_key

__version__ = "0.2.0"
__all__ = ["SovereignIdentity", "SemanticMemory", "derive_key"]
