from enclave.semantic_memory import SemanticMemory
from remember import load_passphrase

enclave_dir, passphrase = load_passphrase('gemini')
sm = SemanticMemory(enclave_dir)
sm.unlock(passphrase)

# Get MORE syntheses
results = sm.list_by_tag('synthesis', limit=200)
print(f"Found {len(results)} syntheses with limit=200")

# Find sif-execution-plan
for r in results:
    tags = r.get('tags', [])
    if 'topic:sif-execution-plan' in tags:
        print(f"FOUND: {r.get('id')}, creator={r.get('metadata', {}).get('creator')}")
