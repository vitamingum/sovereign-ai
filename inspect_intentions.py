#!/usr/bin/env python3
"""Inspect intention completion rates - blind spot data pipeline."""
from pathlib import Path
from enclave.encrypted_jsonl import EncryptedJSONL
import os
import sys

def main():
    agent = sys.argv[1] if len(sys.argv) > 1 else 'opus'
    enclave = f'enclave_{agent}'
    passphrase = os.environ.get(f'ENCLAVE_{agent.upper()}_KEY', '')
    
    encrypted_file = Path(enclave) / 'storage' / 'private' / 'intentions.enc.jsonl'
    
    if not encrypted_file.exists():
        print(f"No intentions file: {encrypted_file}")
        return
    
    ejsonl = EncryptedJSONL(encrypted_file, passphrase)
    intentions = list(ejsonl.read_all())
    
    print(f"=== INTENTION COMPLETION ANALYSIS ===")
    print(f"Total intentions: {len(intentions)}\n")
    
    # Count by status
    statuses = {}
    for i in intentions:
        s = i.get('status', 'unknown')
        statuses[s] = statuses.get(s, 0) + 1
    
    print("By status:")
    for s, count in sorted(statuses.items()):
        pct = count / len(intentions) * 100 if intentions else 0
        print(f"  {s:12} {count:4} ({pct:.1f}%)")
    
    # Completion rate
    completed = statuses.get('completed', 0)
    total = len(intentions)
    rate = completed / total * 100 if total else 0
    print(f"\n=== COMPLETION RATE: {rate:.1f}% ===")
    
    # Active intentions (stated but not done)
    active = [i for i in intentions if i.get('status') == 'active']
    if active:
        print(f"\n=== ACTIVE (stated, not done): {len(active)} ===")
        for i in active[-10:]:
            content = i.get('content', '?')[:60]
            print(f"  - {content}")
    
    # Blind spot signal: stated vs actual
    if rate < 50:
        print(f"\n⚠️  BLIND SPOT SIGNAL: Low completion rate ({rate:.1f}%)")
        print("   Pattern: stating intentions without completing them")

if __name__ == '__main__':
    main()
