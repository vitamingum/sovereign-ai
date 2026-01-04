from enclave.semantic_memory import SemanticMemory
from remember import load_passphrase

enclave_dir, passphrase = load_passphrase('gemini')
sm = SemanticMemory(enclave_dir)
sm.unlock(passphrase)

# Get specific entry
results = sm.list_by_tag('topic:logic-parity-testing', limit=10)
for r in results:
    print(f"ID: {r['id']}")
    print(f"Timestamp: {r.get('timestamp')}")
    print(f"Creator: {r.get('metadata', {}).get('creator', 'UNKNOWN')}")
    print(f"Text: {r.get('text', '')[:200]}...")
    print("-" * 50)
