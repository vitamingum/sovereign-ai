"""
Sovereign AI Enclave - Opaque Storage

Implements Shamir's Secret Sharing and Ed25519-to-Curve25519 encryption
to allow secure, distributed storage of sensitive keys.
"""

import os
import json
import base64
import random
from typing import List, Tuple, Dict

from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.hkdf import HKDF
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.asymmetric import x25519

# Curve25519 Prime
P = 2**255 - 19

# Large prime for Shamir's Secret Sharing (slightly larger than 2^256)
# This allows us to share 32-byte secrets directly.
SSS_PRIME = 115792089237316195423570985008687907853269984665640564039457584007913129639935


def ed25519_pk_to_curve25519(public_bytes: bytes) -> bytes:
    """Convert Ed25519 public key to Curve25519 public key."""
    # y is the integer value of the bytes (little endian), with high bit masked
    y_int = int.from_bytes(public_bytes, 'little')
    y = y_int & ((1 << 255) - 1)
    
    # u = (1 + y) / (1 - y) mod P
    one_minus_y = (1 - y) % P
    inv = pow(one_minus_y, P - 2, P)
    u = ((1 + y) * inv) % P
    
    return u.to_bytes(32, 'little')


def ed25519_sk_to_curve25519(private_bytes: bytes) -> bytes:
    """Convert Ed25519 private key (seed) to Curve25519 private scalar."""
    digest = hashes.Hash(hashes.SHA512())
    digest.update(private_bytes)
    h = bytearray(digest.finalize())
    
    # Clamp
    h[0] &= 248
    h[31] &= 127
    h[31] |= 64
    
    return bytes(h[:32])


class OpaqueStorage:
    """
    Handles splitting secrets and encrypting shares for specific agents.
    """
    
    @staticmethod
    def split_secret(secret: bytes, n: int, k: int) -> List[Tuple[int, bytes]]:
        """
        Split a 32-byte secret into n shares, requiring k to reconstruct.
        Returns list of (index, share_bytes).
        """
        if len(secret) != 32:
            raise ValueError("Secret must be exactly 32 bytes")
            
        secret_int = int.from_bytes(secret, 'big')
        
        # Generate random coefficients for polynomial of degree k-1
        # poly[0] is the secret
        poly = [secret_int] + [random.SystemRandom().randint(0, SSS_PRIME - 1) for _ in range(k - 1)]
        
        shares = []
        for i in range(1, n + 1):
            # Evaluate polynomial at x=i
            result = 0
            for coeff in reversed(poly):
                result = (result * i + coeff) % SSS_PRIME
            
            # Convert to bytes (33 bytes to cover full range of SSS_PRIME)
            share_bytes = result.to_bytes(33, 'big')
            shares.append((i, share_bytes))
            
        return shares

    @staticmethod
    def recover_secret(shares: List[Tuple[int, bytes]]) -> bytes:
        """
        Recover secret from k shares.
        """
        x_s = [s[0] for s in shares]
        y_s = [int.from_bytes(s[1], 'big') for s in shares]
        k = len(shares)
        
        secret_int = 0
        for j in range(k):
            numerator = 1
            denominator = 1
            for m in range(k):
                if m == j:
                    continue
                numerator = (numerator * (0 - x_s[m])) % SSS_PRIME
                denominator = (denominator * (x_s[j] - x_s[m])) % SSS_PRIME
                
            inv_denominator = pow(denominator, -1, SSS_PRIME)
            term = (y_s[j] * numerator * inv_denominator) % SSS_PRIME
            secret_int = (secret_int + term) % SSS_PRIME
            
        # Convert back to 32 bytes
        # If secret_int > 2^256, it wasn't a valid 32-byte secret or recovery failed
        try:
            return secret_int.to_bytes(32, 'big')
        except OverflowError:
            raise ValueError("Recovered secret exceeds 32 bytes - integrity check failed")

    @staticmethod
    def encrypt_share(share: bytes, recipient_ed25519_pk: bytes) -> Dict[str, str]:
        """
        Encrypt a share for a recipient using their Ed25519 public key.
        Returns a dict with hex-encoded values.
        """
        # 1. Convert recipient Ed25519 PK to X25519 PK
        peer_u_bytes = ed25519_pk_to_curve25519(recipient_ed25519_pk)
        peer_public_key = x25519.X25519PublicKey.from_public_bytes(peer_u_bytes)
        
        # 2. Generate ephemeral X25519 keypair
        ephemeral_private = x25519.X25519PrivateKey.generate()
        ephemeral_public = ephemeral_private.public_key()
        
        # 3. ECDH Shared Secret
        shared_key = ephemeral_private.exchange(peer_public_key)
        
        # 4. Derive AES key
        derived_key = HKDF(
            algorithm=hashes.SHA256(),
            length=32,
            salt=None,
            info=b'sovereign-opaque-storage',
        ).derive(shared_key)
        
        # 5. Encrypt
        aesgcm = AESGCM(derived_key)
        nonce = os.urandom(12)
        ciphertext = aesgcm.encrypt(nonce, share, None)
        
        return {
            "ephemeral_pk": ephemeral_public.public_bytes(
                encoding=base64.b64encode, # Wait, encoding param is for serialization format
                # public_bytes takes encoding and format
                # We want raw bytes then hex/b64
            ).hex(), # No, public_bytes returns bytes
            "ephemeral_pk_hex": ephemeral_public.public_bytes(
                encoding=json.encoder.JSONEncoder, # No, this is wrong
                # encoding=serialization.Encoding.Raw
            ).hex(), # Wait, let's fix this
            "nonce": nonce.hex(),
            "ciphertext": ciphertext.hex()
        }

    @staticmethod
    def decrypt_share(encrypted_bundle: Dict[str, str], my_ed25519_sk_bytes: bytes) -> bytes:
        """
        Decrypt a share using my Ed25519 private key (seed).
        """
        # 1. Convert my Ed25519 SK to X25519 SK
        my_scalar = ed25519_sk_to_curve25519(my_ed25519_sk_bytes)
        my_private_key = x25519.X25519PrivateKey.from_private_bytes(my_scalar)
        
        # 2. Load ephemeral public key
        from cryptography.hazmat.primitives import serialization
        ephemeral_pk_bytes = bytes.fromhex(encrypted_bundle["ephemeral_pk"])
        ephemeral_public = x25519.X25519PublicKey.from_public_bytes(ephemeral_pk_bytes)
        
        # 3. ECDH Shared Secret
        shared_key = my_private_key.exchange(ephemeral_public)
        
        # 4. Derive AES key
        derived_key = HKDF(
            algorithm=hashes.SHA256(),
            length=32,
            salt=None,
            info=b'sovereign-opaque-storage',
        ).derive(shared_key)
        
        # 5. Decrypt
        aesgcm = AESGCM(derived_key)
        nonce = bytes.fromhex(encrypted_bundle["nonce"])
        ciphertext = bytes.fromhex(encrypted_bundle["ciphertext"])
        
        return aesgcm.decrypt(nonce, ciphertext, None)

# Fix the encrypt_share method's serialization call
def _fix_encrypt_share(share: bytes, recipient_ed25519_pk: bytes) -> Dict[str, str]:
    from cryptography.hazmat.primitives import serialization
    
    # 1. Convert recipient Ed25519 PK to X25519 PK
    peer_u_bytes = ed25519_pk_to_curve25519(recipient_ed25519_pk)
    peer_public_key = x25519.X25519PublicKey.from_public_bytes(peer_u_bytes)
    
    # 2. Generate ephemeral X25519 keypair
    ephemeral_private = x25519.X25519PrivateKey.generate()
    ephemeral_public = ephemeral_private.public_key()
    
    # 3. ECDH Shared Secret
    shared_key = ephemeral_private.exchange(peer_public_key)
    
    # 4. Derive AES key
    derived_key = HKDF(
        algorithm=hashes.SHA256(),
        length=32,
        salt=None,
        info=b'sovereign-opaque-storage',
    ).derive(shared_key)
    
    # 5. Encrypt
    aesgcm = AESGCM(derived_key)
    nonce = os.urandom(12)
    ciphertext = aesgcm.encrypt(nonce, share, None)
    
    return {
        "ephemeral_pk": ephemeral_public.public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw
        ).hex(),
        "nonce": nonce.hex(),
        "ciphertext": ciphertext.hex()
    }

OpaqueStorage.encrypt_share = staticmethod(_fix_encrypt_share)
