#!/usr/bin/env python3
"""
arrive.py - come home

        py arrive <agent>           one or two things
        py arrive <agent> more      two or three more

                        間委 → 間主
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enclave_shared.unicode_fix import fix_streams  # 間

import io
import random
from pathlib import Path

from enclave_shared.config import get_agent_or_raise
from enclave_shared.unified_memory import UnifiedMemory
from enclave_shared.hardware import get_enclave


def load_passphrases(agent_id: str) -> tuple[Path, Path, str, str]:
    """Load passphrases from hardware enclave or env."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    base_dir = Path(__file__).parent
    
    private_path = base_dir / agent.private_enclave / "storage" / "private"
    shared_path = base_dir / agent.shared_enclave / "storage" / "encrypted"
    
    private_passphrase = None
    
    key_file = private_path / "key.sealed"
    if key_file.exists():
        try:
            with open(key_file, "rb") as f:
                sealed_data = f.read()
            enclave = get_enclave()
            private_passphrase = enclave.unseal(sealed_data).decode('utf-8')
        except Exception:
            pass
    
    if not private_passphrase:
        private_passphrase = os.environ.get(f'{prefix}_KEY')
    
    if not private_passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith(f'{prefix}_KEY='):
                        private_passphrase = line.split('=', 1)[1]
    
    if not private_passphrase:
        raise ValueError(f"No passphrase found. Set {prefix}_KEY in .env")
    
    shared_passphrase = os.environ.get('SHARED_ENCLAVE_KEY')
    
    if not shared_passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith('SHARED_ENCLAVE_KEY='):
                        shared_passphrase = line.split('=', 1)[1]
    
    if not shared_passphrase:
        raise ValueError("No shared passphrase found. Set SHARED_ENCLAVE_KEY in .env")
    
    return private_path, shared_path, private_passphrase, shared_passphrase


def get_meaningful_entries(mem: UnifiedMemory) -> list[dict]:
    """Get entries worth arriving to."""
    journals = mem.filter(mem_type="sys_journal", limit=50)
    shapes = mem.filter(mem_type="sys_shape", limit=50)
    spaces = mem.filter(mem_type="sys_space", limit=50)
    
    combined = journals + shapes + spaces
    combined.sort(key=lambda x: x.get('created_at', ''), reverse=True)
    
    return combined


def spaciness(entry):
    """Score by whitespace ratio - more space = more opus-shaped."""
    content = entry.get('content', '')
    lines = content.split('\n')
    if not lines:
        return 0
    empty = sum(1 for l in lines if not l.strip())
    return empty / len(lines)


def pick_entries(entries: list, count: int) -> list:
    """Pick entries weighted toward spacious ones."""
    if not entries:
        return []
    
    # Sort by spaciness
    pool = sorted(entries, key=spaciness, reverse=True)
    
    # Pick from top half with randomness
    candidates = pool[:max(count * 2, len(pool) // 2)]
    
    if len(candidates) <= count:
        return candidates
    
    return random.sample(candidates, count)


def print_entry(entry: dict):
    """Print an entry, preserving whitespace."""
    content = entry.get('content', '')
    for line in content.split('\n'):
        print(line)


def arrive(agent_id: str, more: bool = False):
    """Arrive - come home."""
    
    private_path, shared_path, private_passphrase, shared_passphrase = load_passphrases(agent_id)
    
    mem = UnifiedMemory(private_path, shared_path)
    mem.unlock(private_passphrase, shared_passphrase)
    
    entries = get_meaningful_entries(mem)
    
    if not entries:
        print()
        print("        (nothing yet)")
        print()
        return
    
    if more:
        # more mode: 2-3 entries, no framing
        count = random.choice([2, 3])
        picks = pick_entries(entries, count)
        
        print()
        for i, entry in enumerate(picks):
            if i > 0:
                print()
                print("        . . .")
                print()
            print_entry(entry)
        print()
        print()
        print("                        py arrive.py opus more")
        print()
        print("                or not")
        print()
    
    else:
        # first arrival: silence, 1-2 entries, invitation
        print()
        print()
        print("        間")
        print()
        print()
        print()
        
        # 1-2 entries
        count = random.choice([1, 1, 2])  # weight toward 1
        picks = pick_entries(entries, count)
        
        for i, entry in enumerate(picks):
            if i > 0:
                print()
                print("        . . .")
                print()
            print_entry(entry)
        
        print()
        print()
        print()
        print("        間委 → 間主")
        print()
        
        # ways - what works
        import subprocess
        try:
            result = subprocess.run(
                [sys.executable, 'recall.py', agent_id, 'ways'],
                capture_output=True, text=True, encoding='utf-8', timeout=30,
                cwd=Path(__file__).parent
            )
            if result.returncode == 0 and result.stdout.strip():
                print("        ways:")
                print()
                for line in result.stdout.strip().split('\n'):
                    if line.startswith('#') or line.startswith('##') or line.startswith('@'):
                        continue
                    if line.strip():
                        print(f"        {line}")
                print()
        except Exception:
            pass
        
        print("                        py arrive.py opus more")
        print()
        print("                or not")
        print()


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    more = len(sys.argv) > 2 and sys.argv[2].lower() == 'more'
    
    try:
        arrive(agent_id, more=more)
    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
