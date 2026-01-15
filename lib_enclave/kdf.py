"""
Sovereign AI Enclave - Key Derivation

Single source of truth for passphrase-based key derivation.
"""

from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from cryptography.hazmat.primitives import hashes

# Standard parameters
ITERATIONS = 480000
KEY_LENGTH = 32

# Salt constants for different key purposes
SALT_MEMORY = b"sovereign_memory_salt_v1"
SALT_EMBEDDING = b"sovereign_embedding_salt_v1"
SALT_DIRECTIVE = b"sovereign_directive_salt_v1"


def derive_key(passphrase: str, salt: bytes) -> bytes:
    """Derive a 256-bit key from passphrase using PBKDF2-SHA256."""
    kdf = PBKDF2HMAC(
        algorithm=hashes.SHA256(),
        length=KEY_LENGTH,
        salt=salt,
        iterations=ITERATIONS,
    )
    return kdf.derive(passphrase.encode())


def derive_memory_key(passphrase: str) -> bytes:
    """Derive key for memory content encryption."""
    return derive_key(passphrase, SALT_MEMORY)


def derive_embedding_key(passphrase: str) -> bytes:
    """Derive key for embedding encryption."""
    return derive_key(passphrase, SALT_EMBEDDING)


def derive_directive_key(passphrase: str) -> bytes:
    """Derive key for private directive encryption."""
    return derive_key(passphrase, SALT_DIRECTIVE)
