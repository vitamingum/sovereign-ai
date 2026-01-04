from enclave.semantic_memory import SemanticMemory
from remember import load_passphrase
import json
import traceback

enclave_dir, passphrase = load_passphrase('gemini')
sm = SemanticMemory(enclave_dir)
sm.unlock(passphrase)

log_file = sm.private_path / "semantic_memories.jsonl"
with open(log_file) as f:
    lines = [l.strip() for l in f if l.strip()]

# Get the last entry (sif-execution-plan)
last_entry = json.loads(lines[-1])
print(f"ID: {last_entry['id']}")
print(f"Tags: {last_entry['tags']}")

# Try to decrypt it
try:
    content_nonce = bytes.fromhex(last_entry["content_nonce"])
    content_ciphertext = bytes.fromhex(last_entry["content"])
    decrypted = sm._decrypt(content_nonce, content_ciphertext, sm._encryption_key)
    print(f"Decrypted: {decrypted[:200]}...")
except Exception as e:
    print(f"DECRYPT FAILED: {type(e).__name__}: {e}")
    traceback.print_exc()
