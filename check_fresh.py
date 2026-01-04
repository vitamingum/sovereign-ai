from enclave.semantic_memory import SemanticMemory
from remember import load_passphrase
from pathlib import Path

enclave_dir, passphrase = load_passphrase('gemini')

# Create a FRESH instance
sm = SemanticMemory(enclave_dir)
sm.unlock(passphrase)

# Count total
log_file = sm.private_path / "semantic_memories.jsonl"
with open(log_file) as f:
    lines = [l for l in f if l.strip()]
print(f"Raw file has {len(lines)} entries")

# Now list_all
all_mems = sm.list_all()
print(f"list_all returns {len(all_mems)} entries")

# Check for sif-execution-plan
found = [m for m in all_mems if 'topic:sif-execution-plan' in m.get('tags', [])]
print(f"Found {len(found)} with topic:sif-execution-plan")
