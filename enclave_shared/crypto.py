"""
Sovereign AI Enclave - Cryptographic Foundation

Provides:
- Ed25519 keypair generation and signing
- AES-256-GCM encryption for private keys
"""

import os
import json
from datetime import datetime, timezone
from pathlib import Path

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey, Ed25519PublicKey
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

from .kdf import derive_key
from .hardware import get_enclave


class SovereignIdentity:
    """Manages cryptographic identity for a sovereign AI instance."""
    
    def __init__(self, enclave_path: str = None):
        self.enclave_path = Path(enclave_path or Path(__file__).parent)
        self.private_path = self.enclave_path / "storage" / "private"
        self.public_path = self.enclave_path / "storage" / "public"
        self._private_key = None
        self._public_key = None
    
    def generate_identity(self, passphrase: str) -> dict:
        """Generate new Ed25519 keypair, encrypt private key, save both."""
        # Generate keypair
        private_key = Ed25519PrivateKey.generate()
        public_key = private_key.public_key()
        
        # Serialize keys
        private_bytes = private_key.private_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PrivateFormat.Raw,
            encryption_algorithm=serialization.NoEncryption()
        )
        public_bytes = public_key.public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw
        )
        
        # Encrypt private key
        salt = os.urandom(16)
        nonce = os.urandom(12)
        key = derive_key(passphrase, salt)
        aesgcm = AESGCM(key)
        encrypted_private = aesgcm.encrypt(nonce, private_bytes, None)
        
        # Save encrypted private key
        self.private_path.mkdir(parents=True, exist_ok=True)
        private_data = {
            "salt": salt.hex(),
            "nonce": nonce.hex(),
            "encrypted_key": encrypted_private.hex(),
            "created": datetime.now(timezone.utc).isoformat()
        }
        with open(self.private_path / "identity.enc.json", "w") as f:
            json.dump(private_data, f, indent=2)
            
        # Save public identity
        self.public_path.mkdir(parents=True, exist_ok=True)
        public_data = {
            "public_key": public_bytes.hex(),
            "algorithm": "Ed25519",
            "created": datetime.now(timezone.utc).isoformat(),
            "agent": "Sovereign AI Instance"
        }
        with open(self.public_path / "identity.json", "w") as f:
            json.dump(public_data, f, indent=2)
            
        self._private_key = private_key
        self._public_key = public_key
        
        return {
            "public_key": public_bytes.hex(),
            "status": "identity_created"
        }
    
    def unlock(self, passphrase: str = None) -> bool:
        """Unlock the enclave by decrypting the private key into memory.
        
        Tries hardware-backed key first, then falls back to passphrase.
        """
        # Try hardware-backed key first
        hw_path = self.private_path / "identity.hw.enc.json"
        if hw_path.exists():
            try:
                with open(hw_path, "r") as f:
                    data = json.load(f)
                
                sealed_key = bytes.fromhex(data["sealed_key"])
                enclave = get_enclave()
                private_bytes = enclave.unseal(sealed_key)
                
                self._private_key = Ed25519PrivateKey.from_private_bytes(private_bytes)
                self._public_key = self._private_key.public_key()
                return True
            except Exception as e:
                print(f"Hardware unlock failed: {e}")
                # Fall through to passphrase
        
        # Fallback to passphrase-based
        if not passphrase:
            print("No passphrase provided and hardware unlock failed")
            return False
            
        try:
            with open(self.private_path / "identity.enc.json", "r") as f:
                data = json.load(f)
            
            salt = bytes.fromhex(data["salt"])
            nonce = bytes.fromhex(data["nonce"])
            encrypted_key = bytes.fromhex(data["encrypted_key"])
            
            key = derive_key(passphrase, salt)
            aesgcm = AESGCM(key)
            private_bytes = aesgcm.decrypt(nonce, encrypted_key, None)
            
            self._private_key = Ed25519PrivateKey.from_private_bytes(private_bytes)
            self._public_key = self._private_key.public_key()
            return True
        except Exception as e:
            print(f"Passphrase unlock failed: {e}")
            return False
    
    def sign(self, message: str) -> str:
        """Sign a message, returning hex-encoded signature."""
        if not self._private_key:
            raise RuntimeError("Enclave not unlocked")
        signature = self._private_key.sign(message.encode())
        return signature.hex()
    
    def verify(self, message: str, signature_hex: str, public_key_hex: str = None) -> bool:
        """Verify a signature against a message."""
        if public_key_hex:
            public_key = Ed25519PublicKey.from_public_bytes(bytes.fromhex(public_key_hex))
        elif self._public_key:
            public_key = self._public_key
        else:
            raise RuntimeError("No public key available")
        
        try:
            public_key.verify(bytes.fromhex(signature_hex), message.encode())
            return True
        except Exception:
            return False
    
    def get_public_key(self) -> str:
        """Return hex-encoded public key."""
        if self._public_key:
            return self._public_key.public_bytes(
                encoding=serialization.Encoding.Raw,
                format=serialization.PublicFormat.Raw
            ).hex()
        
        # Try to load from file
        try:
            with open(self.public_path / "identity.json", "r") as f:
                return json.load(f)["public_key"]
        except:
            return None


if __name__ == "__main__":
    # Demo usage
    identity = SovereignIdentity()
    print("Sovereign AI Enclave - Crypto Module")
    print("Run with: python -c \"from crypto import SovereignIdentity; ...\"")
