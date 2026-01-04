from enclave.semantic_memory import SemanticMemory
from remember import load_passphrase

enclave_dir, passphrase = load_passphrase('gemini')
sm = SemanticMemory(enclave_dir)
sm.unlock(passphrase)

# Get ALL memories, check the first few (newest)
all_mems = sm.list_all(limit=5)
print(f"Newest 5 entries:")
for m in all_mems:
    topic = [t for t in m.get('tags', []) if t.startswith('topic:')]
    print(f"  {m['id']}: {m['timestamp'][:19]} tags={topic}")
