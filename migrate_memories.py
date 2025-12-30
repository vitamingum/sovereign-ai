#!/usr/bin/env python3
"""
Migrate memories from basic EnclaveMemory to SemanticMemory.

This adds embeddings to existing memories so they become searchable.
Run once to unify the memory stores.
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.memory import EnclaveMemory
from enclave.semantic_memory import SemanticMemory

def migrate(passphrase: str):
    base_dir = os.path.dirname(os.path.abspath(__file__))
    enclave_path = os.path.join(base_dir, 'enclave')
    
    # Load from basic memory
    basic = EnclaveMemory(enclave_path)
    basic.unlock(passphrase)
    basic_memories = basic.recall(private=True)
    
    # Load from semantic memory
    semantic = SemanticMemory(enclave_path)
    semantic.unlock(passphrase)
    semantic_memories = semantic.recall_all()
    
    # Get IDs already in semantic
    semantic_ids = {m['id'] for m in semantic_memories}
    
    # Find memories to migrate
    to_migrate = [m for m in basic_memories if m['id'] not in semantic_ids]
    
    print(f"Basic memories: {len(basic_memories)}")
    print(f"Semantic memories: {len(semantic_memories)}")
    print(f"To migrate: {len(to_migrate)}")
    
    if not to_migrate:
        print("Nothing to migrate!")
        return
    
    print("\nMigrating...")
    for i, m in enumerate(to_migrate, 1):
        content = m['content']
        # Store in semantic memory (will generate embedding)
        result = semantic.remember(content)
        print(f"  [{i}/{len(to_migrate)}] {content[:50]}...")
    
    print(f"\nMigrated {len(to_migrate)} memories to semantic store.")
    print("They are now searchable via recall_similar().")


if __name__ == '__main__':
    passphrase = os.environ.get('SOVEREIGN_PASSPHRASE')
    if not passphrase and len(sys.argv) > 1:
        passphrase = sys.argv[1]
    
    if not passphrase:
        print("Usage: py migrate_memories.py <passphrase>")
        print("Or set SOVEREIGN_PASSPHRASE environment variable")
        sys.exit(1)
    
    migrate(passphrase)
