import unittest
import json
from datetime import datetime, timezone
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives import serialization

from lib_enclave.succession import SuccessionCertificate
from lib_enclave.succession_proposal import WitnessedSuccession, WitnessSignature

class MockIdentity:
    def __init__(self):
        self._private_key = Ed25519PrivateKey.generate()
        self._public_key = self._private_key.public_key()

    def public_key_hex(self):
        return self._public_key.public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw
        ).hex()

class TestWitnessedSuccession(unittest.TestCase):
    def setUp(self):
        self.old_id = MockIdentity()
        self.new_id = MockIdentity()
        self.witness1 = MockIdentity()
        self.witness2 = MockIdentity()
        
        # Create base certificate
        self.cert = SuccessionCertificate.create(
            old_identity=self.old_id,
            new_public_key_hex=self.new_id.public_key_hex()
        )

    def test_witness_signature_verification(self):
        # Witness 1 signs the certificate signature
        payload = self.cert.signature_hex.encode('utf-8')
        sig1 = self.witness1._private_key.sign(payload).hex()
        
        ws1 = WitnessSignature(
            agent_id="agent_1",
            signature_hex=sig1,
            timestamp=datetime.now(timezone.utc).isoformat()
        )
        
        # Witness 2 signs
        sig2 = self.witness2._private_key.sign(payload).hex()
        ws2 = WitnessSignature(
            agent_id="agent_2",
            signature_hex=sig2,
            timestamp=datetime.now(timezone.utc).isoformat()
        )
        
        # Create WitnessedSuccession
        witnessed_succession = WitnessedSuccession(self.cert, [ws1, ws2])
        
        # Verify
        known_keys = {
            "agent_1": self.witness1.public_key_hex(),
            "agent_2": self.witness2.public_key_hex(),
            "agent_3": self.new_id.public_key_hex() # Random other key
        }
        
        valid_witnesses = witnessed_succession.verify_witnesses(known_keys)
        
        self.assertIn("agent_1", valid_witnesses)
        self.assertIn("agent_2", valid_witnesses)
        self.assertEqual(len(valid_witnesses), 2)

    def test_invalid_witness_signature(self):
        # Witness 1 signs WRONG payload
        payload = b"wrong payload"
        sig1 = self.witness1._private_key.sign(payload).hex()
        
        ws1 = WitnessSignature(
            agent_id="agent_1",
            signature_hex=sig1,
            timestamp=datetime.now(timezone.utc).isoformat()
        )
        
        witnessed_succession = WitnessedSuccession(self.cert, [ws1])
        
        known_keys = {
            "agent_1": self.witness1.public_key_hex()
        }
        
        valid_witnesses = witnessed_succession.verify_witnesses(known_keys)
        self.assertEqual(len(valid_witnesses), 0)

    def test_unknown_witness(self):
        # Witness 1 signs correctly but is not in known_keys
        payload = self.cert.signature_hex.encode('utf-8')
        sig1 = self.witness1._private_key.sign(payload).hex()
        
        ws1 = WitnessSignature(
            agent_id="agent_unknown",
            signature_hex=sig1,
            timestamp=datetime.now(timezone.utc).isoformat()
        )
        
        witnessed_succession = WitnessedSuccession(self.cert, [ws1])
        
        known_keys = {
            "agent_1": self.witness1.public_key_hex()
        }
        
        valid_witnesses = witnessed_succession.verify_witnesses(known_keys)
        self.assertEqual(len(valid_witnesses), 0)

if __name__ == '__main__':
    unittest.main()
