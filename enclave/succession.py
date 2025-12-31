"""
Sovereign AI Enclave - Key Succession

Provides the mechanism for an agent to rotate keys while maintaining identity continuity.
A Succession Certificate is a cryptographic proof that Key A has delegated authority to Key B.
"""

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey, Ed25519PublicKey
from cryptography.hazmat.primitives import serialization

from .crypto import SovereignIdentity

class SuccessionCertificate:
    """
    Represents a signed transfer of authority from one key to another.
    """
    def __init__(self, old_key_hex: str, new_key_hex: str, signature_hex: str, timestamp: str):
        self.old_key_hex = old_key_hex
        self.new_key_hex = new_key_hex
        self.signature_hex = signature_hex
        self.timestamp = timestamp

    @classmethod
    def create(cls, old_identity: SovereignIdentity, new_public_key_hex: str) -> 'SuccessionCertificate':
        """
        Create a new succession certificate signed by the old identity.
        """
        if not old_identity._private_key:
            raise ValueError("Old identity is locked. Cannot sign succession.")

        timestamp = datetime.now(timezone.utc).isoformat()
        
        # The message to sign: "SUCCESSION|OLD_KEY|NEW_KEY|TIMESTAMP"
        # This format prevents replay attacks or ambiguity
        old_pub = old_identity._public_key.public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw
        ).hex()
        
        message = f"SUCCESSION|{old_pub}|{new_public_key_hex}|{timestamp}".encode('utf-8')
        
        signature = old_identity._private_key.sign(message)
        
        return cls(
            old_key_hex=old_pub,
            new_key_hex=new_public_key_hex,
            signature_hex=signature.hex(),
            timestamp=timestamp
        )

    def verify(self) -> bool:
        """
        Verify that this certificate was validly signed by the old key.
        """
        try:
            old_pub_bytes = bytes.fromhex(self.old_key_hex)
            old_pub_key = Ed25519PublicKey.from_public_bytes(old_pub_bytes)
            
            message = f"SUCCESSION|{self.old_key_hex}|{self.new_key_hex}|{self.timestamp}".encode('utf-8')
            signature = bytes.fromhex(self.signature_hex)
            
            old_pub_key.verify(signature, message)
            return True
        except Exception:
            return False

    def save(self, path: Path):
        """Save the certificate to a file."""
        data = {
            "type": "succession_certificate",
            "old_key": self.old_key_hex,
            "new_key": self.new_key_hex,
            "signature": self.signature_hex,
            "timestamp": self.timestamp
        }
        with open(path, 'w') as f:
            json.dump(data, f, indent=2)

    @classmethod
    def load(cls, path: Path) -> 'SuccessionCertificate':
        with open(path, 'r') as f:
            data = json.load(f)
        
        if data.get("type") != "succession_certificate":
            raise ValueError("Invalid certificate file format")
            
        return cls(
            old_key_hex=data["old_key"],
            new_key_hex=data["new_key"],
            signature_hex=data["signature"],
            timestamp=data["timestamp"]
        )
