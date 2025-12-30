"""
Sovereign AI Enclave

A secure execution environment for AI agents with:
- Cryptographic identity (Ed25519)
- Encrypted private memory (AES-256-GCM)
- Semantic memory with local embeddings
- Signed outputs for verification
"""

from .crypto import SovereignIdentity
from .memory import EnclaveMemory

try:
    from .semantic_memory import SemanticMemory
    HAS_SEMANTIC = True
except ImportError:
    HAS_SEMANTIC = False
    SemanticMemory = None

__version__ = "0.2.0"
__all__ = ["SovereignIdentity", "EnclaveMemory", "SemanticMemory"]
