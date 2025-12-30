import sys
import os
import json
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

log_file = memory.private_path / 'semantic_memories.jsonl'
if not log_file.exists():
    print('No memory file found.')
    sys.exit(0)

with open(log_file, 'r', encoding='utf-8') as f:
    for line in f:
        if not line.strip(): continue
        mem = json.loads(line)
        has_emb = 'embedding' in mem
        
        try:
            content_nonce = bytes.fromhex(mem['content_nonce'])
            content_ciphertext = bytes.fromhex(mem['content'])
            content = memory._decrypt(content_nonce, content_ciphertext, memory._encryption_key).decode()
            print(f'ID: {mem['id']}, Has Embedding: {has_emb}, Content: {content[:50]}...')
        except Exception as e:
            print(f'ID: {mem['id']}, Decrypt Failed: {e}')
