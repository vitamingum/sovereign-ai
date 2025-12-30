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

print(f'Querying memory in {enclave_dir}...')
memory = SemanticMemory(enclave_dir)
memory.unlock(passphrase)

query = 'what I care about, what matters, values'
print(f'Query: {query}')
results = memory.recall_similar(query)

if not results:
    print('No matching memories found.')
else:
    for r in results:
        print(f'- {r['content']} (score: {r['score']:.2f})')
