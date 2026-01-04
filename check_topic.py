from enclave.semantic_memory import SemanticMemory
from remember import load_passphrase

enclave_dir, passphrase = load_passphrase('gemini')
sm = SemanticMemory(enclave_dir)
sm.unlock(passphrase)

results = sm.list_by_tag('topic:sif-execution-plan', limit=10)
print(f"Found {len(results)} entries with topic:sif-execution-plan")
for r in results:
    print(f"  {r.get('id')}: {r.get('metadata', {}).get('creator')}")
