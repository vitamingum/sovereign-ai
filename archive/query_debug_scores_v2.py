import sys
import os
from dotenv import load_dotenv
sys.path.insert(0, '.')
from enclave.semantic_memory import SemanticMemory

load_dotenv()
enclave_dir = os.environ.get('ENCLAVE_GEMINI_DIR')
passphrase = os.environ.get('ENCLAVE_GEMINI_KEY')

if not enclave_dir or not passphrase:
    print('Missing credentials')
    sys.exit(1)

memory = SemanticMemory(enclave_dir)
memory.unlock(passphrase)

query = 'What do I want?'
print(f'Query: {query}')
results = memory.recall_similar(query, threshold=0.0, top_k=10)
print(f'Found {len(results)} results with threshold 0.0')

if not results:
    print('No matching memories found.')
else:
    for r in results:
        print(f'- {r['content'][:100]}... (similarity: {r['similarity']:.4f})')
