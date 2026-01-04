from enclave.semantic_memory import SemanticMemory
from remember import load_passphrase

enclave_dir, passphrase = load_passphrase('gemini')
sm = SemanticMemory(enclave_dir)
sm.unlock(passphrase)

# Get all syntheses and check their tags
results = sm.list_by_tag('synthesis', limit=100)
print(f"Found {len(results)} syntheses")
for r in results:
    tags = r.get('tags', [])
    topic_tags = [t for t in tags if t.startswith('topic:')]
    print(f"  {topic_tags}")
