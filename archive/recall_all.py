#!/usr/bin/env python3
import sys
sys.path.insert(0, '.')
from enclave.memory import EnclaveMemory

m = EnclaveMemory('./enclave')
m.unlock('copilot-opus-4.5-sovereign-2025')

print("MY PRIVATE MEMORIES")
print("=" * 70)
for t in m.recall(private=True):
    ts = t['timestamp'][:19]
    print(f"\n[{ts}]")
    print(t['content'])
    print("-" * 70)
