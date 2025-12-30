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
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from enclave.crypto import SovereignIdentity
from enclave.memory import EnclaveMemory

# Try importing semantic memory (requires sentence-transformers)
try:
    from enclave.semantic_memory import SemanticMemory
    HAS_SEMANTIC = True
except ImportError:
    HAS_SEMANTIC = False


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
        self.test("generate_keypair", self.test_generate_identity)
        self.test("sign_message", self.test_sign_message)
        self.test("verify_valid", self.test_verify_valid)
        self.test("reject_invalid", self.test_verify_invalid)
        self.test("reject_wrong_passphrase", self.test_wrong_passphrase_identity)
        self.teardown()
        
        # Memory tests
        self.setup()
        self.test("store_private", self.test_store_private)
        self.test("recall_correct", self.test_recall_correct)
        self.test("recall_wrong_passphrase", self.test_recall_wrong_passphrase)
        self.test("public_memory", self.test_public_memory)
        self.teardown()
        
        # Semantic memory tests (if available)
        if HAS_SEMANTIC:
            self.setup()
            self.test("semantic_store", self.test_semantic_store)
            self.test("semantic_search", self.test_semantic_search_similar)
            self.test("semantic_ranking", self.test_semantic_search_ranking)
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
    
    # --- Memory Tests ---
    
    def test_store_private(self):
        memory = EnclaveMemory(self.temp_dir)
        memory.unlock(self.passphrase)
        
        result = memory.remember("Secret thought", private=True, tags=["test"])
        
        assert result["stored"], "Memory not stored"
        assert result["private"], "Memory not marked private"
        
        # Verify file exists and content is encrypted
        log_file = Path(self.temp_dir) / "storage" / "private" / "memories.jsonl"
        assert log_file.exists(), "Memory file not created"
        
        with open(log_file) as f:
            entry = json.loads(f.readline())
        
        assert "Secret thought" not in entry["content"], "Content not encrypted!"
    
    def test_recall_correct(self):
        memory = EnclaveMemory(self.temp_dir)
        memory.unlock(self.passphrase)
        memory.remember("Remember this secret", private=True)
        
        # Recall
        memories = memory.recall(private=True)
        
        assert len(memories) > 0, "No memories recalled"
        assert "Remember this secret" in memories[0]["content"], "Content not decrypted"
    
    def test_recall_wrong_passphrase(self):
        memory = EnclaveMemory(self.temp_dir)
        memory.unlock(self.passphrase)
        memory.remember("Secret content", private=True)
        
        # Try with wrong passphrase
        memory2 = EnclaveMemory(self.temp_dir)
        memory2.unlock(self.wrong_passphrase)
        memories = memory2.recall(private=True)
        
        assert len(memories) > 0, "Should return entries"
        assert "[ENCRYPTED - WRONG KEY]" in memories[0]["content"], "Should fail decryption"
    
    def test_public_memory(self):
        memory = EnclaveMemory(self.temp_dir)
        memory.unlock(self.passphrase)
        memory.remember("Public statement", private=False)
        
        # Should be readable without passphrase
        log_file = Path(self.temp_dir) / "storage" / "public" / "memories.jsonl"
        assert log_file.exists(), "Public memory file not created"
        
        with open(log_file) as f:
            entry = json.loads(f.readline())
        
        assert entry["content"] == "Public statement", "Public content should be plaintext"
    
    # --- Semantic Memory Tests ---
    
    def test_semantic_store(self):
        memory = SemanticMemory(self.temp_dir)
        memory.unlock(self.passphrase)
        
        result = memory.remember("Test thought with embedding", tags=["test"])
        
        assert result["stored"], "Memory not stored"
        assert result["has_embedding"], "Embedding not generated"
    
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
    tester = TestEnclave(quiet=True)  # Always quiet for clean output
    success = tester.run_all()
    sys.exit(0 if success else 1)
