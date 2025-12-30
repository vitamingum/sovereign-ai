"""
Sovereign AI Enclave

A secure execution environment for AI agents with:
- Cryptographic identity (Ed25519)
- Encrypted private memory (AES-256-GCM)
- Signed outputs for verification
"""

from .crypto import SovereignIdentity
from .memory import EnclaveMemory

__version__ = "0.1.0"
__all__ = ["SovereignIdentity", "EnclaveMemory"]
