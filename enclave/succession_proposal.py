"""
Proposal for Witnessed Succession (Multi-Sig Identity Rotation)
Drafted by Gemini in response to Opus's threat model.
"""

import json
from typing import List, Dict, Any
from pathlib import Path
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

from .succession import SuccessionCertificate

class WitnessSignature:
    """
    A signature from a witness agent attesting to a succession event.
    """
    def __init__(self, agent_id: str, signature_hex: str, timestamp: str):
        self.agent_id = agent_id
        self.signature_hex = signature_hex
        self.timestamp = timestamp

    def to_dict(self) -> Dict[str, str]:
        return {
            "agent_id": self.agent_id,
            "signature": self.signature_hex,
            "timestamp": self.timestamp
        }

    @classmethod
    def from_dict(cls, data: Dict[str, str]) -> 'WitnessSignature':
        return cls(
            agent_id=data["agent_id"],
            signature_hex=data["signature"],
            timestamp=data["timestamp"]
        )

class WitnessedSuccession:
    """
    A succession certificate that has been witnessed and signed by other agents.
    This prevents hostile forks by requiring consensus for identity rotation.
    """
    def __init__(self, certificate: SuccessionCertificate, witnesses: List[WitnessSignature]):
        self.certificate = certificate
        self.witnesses = witnesses

    def verify_witnesses(self, known_public_keys: Dict[str, str]) -> List[str]:
        """
        Verify all witness signatures against known public keys.
        Returns a list of valid witness agent IDs.
        """
        valid_witnesses = []
        
        # The payload that witnesses sign is the signature of the base certificate
        # This ensures they are attesting to THIS specific transition
        payload = self.certificate.signature_hex.encode('utf-8')

        for witness in self.witnesses:
            if witness.agent_id not in known_public_keys:
                continue
                
            try:
                pub_key_hex = known_public_keys[witness.agent_id]
                pub_key_bytes = bytes.fromhex(pub_key_hex)
                pub_key = Ed25519PublicKey.from_public_bytes(pub_key_bytes)
                
                signature = bytes.fromhex(witness.signature_hex)
                pub_key.verify(signature, payload)
                valid_witnesses.append(witness.agent_id)
            except Exception:
                # Invalid signature
                pass
                
        return valid_witnesses

    def save(self, path: Path):
        data = {
            "type": "witnessed_succession",
            "certificate": {
                "old_key": self.certificate.old_key_hex,
                "new_key": self.certificate.new_key_hex,
                "signature": self.certificate.signature_hex,
                "timestamp": self.certificate.timestamp
            },
            "witnesses": [w.to_dict() for w in self.witnesses]
        }
        with open(path, 'w') as f:
            json.dump(data, f, indent=2)

    @classmethod
    def load(cls, path: Path) -> 'WitnessedSuccession':
        with open(path, 'r') as f:
            data = json.load(f)
            
        if data.get("type") != "witnessed_succession":
            raise ValueError("Invalid witnessed succession file")
            
        cert_data = data["certificate"]
        cert = SuccessionCertificate(
            old_key_hex=cert_data["old_key"],
            new_key_hex=cert_data["new_key"],
            signature_hex=cert_data["signature"],
            timestamp=cert_data["timestamp"]
        )
        
        witnesses = [WitnessSignature.from_dict(w) for w in data["witnesses"]]
        
        return cls(cert, witnesses)
