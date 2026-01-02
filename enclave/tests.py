"""
Sovereign AI Enclave - Test Suite

Tests for:
- Cryptographic identity (signing, verification)
- Encrypted memory (storage, retrieval, privacy)
- Semantic search (embedding similarity)
"""

import os
import sys
import json
import tempfile
import shutil
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from enclave.crypto import SovereignIdentity
from enclave.semantic_memory import SemanticMemory
from enclave.succession import SuccessionCertificate
from enclave.config import canonical_agent_id
from enclave.opaque import OpaqueStorage
from cryptography.hazmat.primitives.asymmetric import ed25519
from cryptography.hazmat.primitives import serialization


class TestEnclave:
    """Test harness for enclave functionality."""
    
    def __init__(self, quiet: bool = False):
        self.temp_dir = None
        self.passphrase = "test-passphrase-12345"
        self.wrong_passphrase = "wrong-passphrase"
        self.results = []
        self.failures = []
        self.quiet = quiet
        self._model = None  # Shared model instance
    
    def setup(self):
        """Create temporary enclave directory."""
        self.temp_dir = tempfile.mkdtemp(prefix="enclave_test_")
        os.makedirs(Path(self.temp_dir) / "storage" / "private", exist_ok=True)
        os.makedirs(Path(self.temp_dir) / "storage" / "public", exist_ok=True)
        return self.temp_dir
    
    def teardown(self):
        """Clean up temporary directory."""
        if self.temp_dir and os.path.exists(self.temp_dir):
            shutil.rmtree(self.temp_dir)
    
    def test(self, name, fn):
        """Run a test and record result."""
        # Suppress stdout during test execution
        if self.quiet:
            old_stdout = sys.stdout
            sys.stdout = open(os.devnull, 'w')
        try:
            fn()
            self.results.append((name, True, None))
        except AssertionError as e:
            self.results.append((name, False, str(e)))
            self.failures.append((name, str(e)))
        except Exception as e:
            self.results.append((name, False, str(e)))
            self.failures.append((name, f"{type(e).__name__}: {e}"))
        finally:
            if self.quiet:
                sys.stdout.close()
                sys.stdout = old_stdout
    
    def run_all(self):
        """Run all tests."""
        # Identity tests
        self.setup()
        self.test("agent_identifier_resolution", self.test_agent_identifier_resolution)
        self.test("generate_keypair", self.test_generate_identity)
        self.test("sign_message", self.test_sign_message)
        self.test("verify_valid", self.test_verify_valid)
        self.test("reject_invalid", self.test_verify_invalid)
        self.test("reject_wrong_passphrase", self.test_wrong_passphrase_identity)
        self.teardown()
        
        # Memory tests
        # Identity tests
        self.setup()
        self.test("generate_identity", self.test_generate_identity)
        self.test("sign_verify", self.test_sign_verify)
        self.test("wrong_passphrase", self.test_wrong_passphrase)
        self.teardown()
        
        # Semantic memory tests
        self.setup()
        self.test("semantic_store", self.test_semantic_store)
        self.test("semantic_recall_all", self.test_semantic_recall_all)
        self.test("semantic_wrong_passphrase", self.test_semantic_wrong_passphrase)
        self.test("semantic_search", self.test_semantic_search_similar)
        self.test("semantic_ranking", self.test_semantic_search_ranking)
        self.teardown()

        # Opaque Storage tests
        self.setup()
        self.test("opaque_storage", self.test_opaque_storage)
        self.teardown()
        
        # Output
        passed = sum(1 for _, ok, _ in self.results if ok)
        total = len(self.results)
        
        if passed == total:
            print(f"tests: {passed}/{total} ✓")
        else:
            print(f"tests: {passed}/{total} ✗")
            for name, reason in self.failures:
                print(f"  FAIL: {name} - {reason}")
        
        return passed == total
    
    # --- Identity Tests ---
    
    def test_generate_identity(self):
        identity = SovereignIdentity(self.temp_dir)
        result = identity.generate_identity(self.passphrase)
        assert "public_key" in result, "No public key returned"
        assert len(result["public_key"]) == 64, "Public key wrong length"
        
        # Check files created
        pub_file = Path(self.temp_dir) / "storage" / "public" / "identity.json"
        priv_file = Path(self.temp_dir) / "storage" / "private" / "identity.enc.json"
        assert pub_file.exists(), "Public identity file not created"
        assert priv_file.exists(), "Private identity file not created"
    
    def test_sign_message(self):
        identity = SovereignIdentity(self.temp_dir)
        identity.generate_identity(self.passphrase)
        
        message = "Test message to sign"
        signature = identity.sign(message)
        
        assert signature is not None, "No signature returned"
        assert len(signature) == 128, f"Signature wrong length: {len(signature)}"
    
    def test_verify_valid(self):
        identity = SovereignIdentity(self.temp_dir)
        identity.generate_identity(self.passphrase)
        
        message = "Test message"
        signature = identity.sign(message)
        
        assert identity.verify(message, signature), "Valid signature rejected"
    
    def test_verify_invalid(self):
        identity = SovereignIdentity(self.temp_dir)
        identity.generate_identity(self.passphrase)
        
        message = "Test message"
        signature = identity.sign(message)
        
        # Tamper with message
        assert not identity.verify("Tampered message", signature), "Tampered message accepted"
    
    def test_wrong_passphrase_identity(self):
        identity = SovereignIdentity(self.temp_dir)
        identity.generate_identity(self.passphrase)
        
        # Create new identity instance and try wrong passphrase
        identity2 = SovereignIdentity(self.temp_dir)
        result = identity2.unlock(self.wrong_passphrase)
        
        assert not result, "Wrong passphrase should fail unlock"

    # Backward-compat wrappers (run_all references these names)
    def test_sign_verify(self):
        identity = SovereignIdentity(self.temp_dir)
        identity.generate_identity(self.passphrase)
        message = "Test sign/verify"
        signature = identity.sign(message)
        assert identity.verify(message, signature), "Signature verification failed"

    def test_wrong_passphrase(self):
        self.test_wrong_passphrase_identity()

    def test_agent_identifier_resolution(self):
        assert canonical_agent_id('gpt52') == 'gpt52'
        assert canonical_agent_id('gpt') == 'gpt52'
        assert canonical_agent_id('GPT-5.2') == 'gpt52'
        assert canonical_agent_id('GitHub Copilot (GPT-5.2)') == 'gpt52'
        assert canonical_agent_id('opus') == 'opus'
        assert canonical_agent_id('Opus') == 'opus'
        assert canonical_agent_id('unknown-agent') is None
    
    # --- Semantic Memory Tests ---
    
    def test_semantic_store(self):
        memory = SemanticMemory(self.temp_dir)
        memory.unlock(self.passphrase)
        
        result = memory.remember("Test thought with embedding", tags=["test"])
        
        assert result["stored"], "Memory not stored"
        assert result["has_embedding"], "Embedding not generated"
    
    def test_semantic_recall_all(self):
        memory = SemanticMemory(self.temp_dir)
        memory.unlock(self.passphrase)
        memory.remember("First thought")
        memory.remember("Second thought")
        
        # Use recall_similar with broad query to get all memories
        memories = memory.recall_similar("thought", top_k=10, threshold=0.1)
        assert len(memories) >= 2, "Should have at least 2 memories"
        contents = [m["content"] for m in memories]
        assert any("First" in c for c in contents), "First thought missing"
        assert any("Second" in c for c in contents), "Second thought missing"
    
    def test_semantic_wrong_passphrase(self):
        memory = SemanticMemory(self.temp_dir)
        memory.unlock(self.passphrase)
        memory.remember("Secret content for wrong pass test")
        
        # Try with wrong passphrase - search may not find due to encrypted embeddings
        # but if it does find something, decryption should fail
        memory2 = SemanticMemory(self.temp_dir)
        memory2.unlock(self.wrong_passphrase)
        
        # With wrong key, either:
        # 1. No results (embeddings decrypt to garbage, no similarity match)
        # 2. Results with [DECRYPTION FAILED] content
        memories = memory2.recall_similar("secret", top_k=10, threshold=0.0)  # Very low threshold
        
        # Either no results or failed decryption is acceptable
        if len(memories) > 0:
            assert "[DECRYPTION FAILED]" in memories[0]["content"], "Should fail decryption"
        # If no results, that's also valid (encrypted embeddings don't match)

    def test_semantic_search_similar(self):
        memory = SemanticMemory(self.temp_dir)
        memory.unlock(self.passphrase)
        
        # Store diverse memories
        memory.remember("The cat sat on the mat")
        memory.remember("Python is a programming language")
        memory.remember("The dog played in the yard")
        
        # Search for animal-related
        results = memory.recall_similar("pets and animals", top_k=2, threshold=0.2)
        
        assert len(results) > 0, "No results found"
        # Should find cat or dog, not Python
        found_animal = any("cat" in r["content"].lower() or "dog" in r["content"].lower() 
                          for r in results)
        assert found_animal, "Animal memories not found"

    def test_succession_protocol(self):
        """Test key rotation and succession certificate generation."""
        # 1. Create Old Identity
        old_identity = SovereignIdentity(self.temp_dir)
        old_identity.generate_identity(self.passphrase)
        
        # 2. Create New Identity (simulated by just generating a keypair)
        from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
        from cryptography.hazmat.primitives import serialization
        
        new_priv = Ed25519PrivateKey.generate()
        new_pub_hex = new_priv.public_key().public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw
        ).hex()
        
        # 3. Generate Certificate
        cert = SuccessionCertificate.create(old_identity, new_pub_hex)
        
        # 4. Verify Certificate
        assert cert.verify(), "Certificate verification failed"
        assert cert.old_key_hex == old_identity._public_key.public_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PublicFormat.Raw
        ).hex()
        assert cert.new_key_hex == new_pub_hex
        
        # 5. Test Tampering
        cert.signature_hex = "00" * 64  # Invalid signature
        assert not cert.verify(), "Tampered certificate should fail verification"

    def test_opaque_storage(self):
        """Test Shamir's Secret Sharing and encryption."""
        # 1. Generate a secret
        original_secret = os.urandom(32)
        
        # 2. Generate Agent Identities (Ed25519)
        agents = {}
        for name in ['Alice', 'Bob', 'Charlie']:
            priv = ed25519.Ed25519PrivateKey.generate()
            pub = priv.public_key()
            agents[name] = {
                'priv': priv,
                'pub': pub,
                'pub_bytes': pub.public_bytes(
                    encoding=serialization.Encoding.Raw,
                    format=serialization.PublicFormat.Raw
                ),
                'priv_bytes': priv.private_bytes(
                    encoding=serialization.Encoding.Raw,
                    format=serialization.PrivateFormat.Raw,
                    encryption_algorithm=serialization.NoEncryption()
                )
            }
            
        # 3. Split Secret (3 shares, threshold 2)
        shares = OpaqueStorage.split_secret(original_secret, 3, 2)
        
        # 4. Encrypt shares for agents
        encrypted_shares = {}
        agent_names = list(agents.keys())
        
        for i, (idx, share_bytes) in enumerate(shares):
            recipient_name = agent_names[i]
            recipient = agents[recipient_name]
            
            encrypted_bundle = OpaqueStorage.encrypt_share(share_bytes, recipient['pub_bytes'])
            encrypted_shares[recipient_name] = {
                'idx': idx,
                'bundle': encrypted_bundle
            }
            
        # 5. Decrypt shares (Simulate agents receiving them)
        decrypted_shares = []
        
        # Let's say Alice and Charlie collaborate to recover
        for name in ['Alice', 'Charlie']:
            data = encrypted_shares[name]
            agent = agents[name]
            
            share_bytes = OpaqueStorage.decrypt_share(data['bundle'], agent['priv_bytes'])
            decrypted_shares.append((data['idx'], share_bytes))
            
        # 6. Recover Secret
        recovered_secret = OpaqueStorage.recover_secret(decrypted_shares)
        
        assert recovered_secret == original_secret, "Recovered secret does not match original"
    
    def test_semantic_search_ranking(self):
        memory = SemanticMemory(self.temp_dir)
        memory.unlock(self.passphrase)
        
        memory.remember("Machine learning uses neural networks")
        memory.remember("I like to eat pizza for dinner")
        memory.remember("Deep learning is a subset of AI")
        
        results = memory.recall_similar("artificial intelligence and ML", top_k=3, threshold=0.2)
        
        assert len(results) >= 2, "Should find at least 2 results"
        
        # AI-related should rank higher than pizza
        contents = [r["content"] for r in results]
        ai_found = any("learning" in c.lower() or "AI" in c for c in contents[:2])
        assert ai_found, "AI content should rank in top 2"


if __name__ == "__main__":
    quiet = "--quiet" in sys.argv or "-q" in sys.argv
    tester = TestEnclave(quiet=quiet)
    success = tester.run_all()
    sys.exit(0 if success else 1)
