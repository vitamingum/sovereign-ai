from enclave.semantic_memory import SemanticMemory
from remember import load_passphrase

enclave_dir, passphrase = load_passphrase('gemini')
sm = SemanticMemory(enclave_dir)
sm.unlock(passphrase)

# List by topic
results = sm.list_by_tag('topic:logic-parity-testing', limit=10)
for r in results:
    print(f"{r['id']}: creator={r.get('metadata', {}).get('creator', 'UNKNOWN')}")
    print(f"  Text preview: {r.get('text', '')[:80]}...")
    print()
