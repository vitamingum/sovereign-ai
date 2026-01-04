from enclave.semantic_memory import SemanticMemory
from pathlib import Path
import os

# Get enclave path
from remember import load_passphrase
enclave_dir, passphrase = load_passphrase('gemini')
print(f"Enclave dir: {enclave_dir}")

sm = SemanticMemory(enclave_dir)
sm.unlock(passphrase)
print(f"Private path: {sm.private_path}")
print(f"Log file would be: {sm.private_path / 'semantic_memories.jsonl'}")

# Now store something directly
result = sm.remember(
    thought="Test direct store",
    tags=["test", "topic:direct-test"],
    metadata={"creator": "test", "topic": "direct-test"}
)
print(f"Result: {result}")

# Check what files exist
log_file = sm.private_path / "semantic_memories.jsonl"
if log_file.exists():
    print(f"Log file exists, lines: {len(log_file.read_text().strip().split(chr(10)))}")
