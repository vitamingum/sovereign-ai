#!/usr/bin/env python3
"""
journal.py - Private reflection space.

Usage:
    py journal.py <agent> "content"           # inline
    py journal.py <agent> -                   # stdin (shape by default)
    py journal.py <agent> --read [limit]

All journal entries are shapes. Form matters.
No prose escape hatch.

Journal wants: feelings, introspection, what it felt like
Journal is: practice being before words
"""

import sys
import os
from pathlib import Path
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enclave_shared.config import get_agent_or_raise
from enclave_shared.unified_memory import UnifiedMemory
from enclave_shared.hardware import get_enclave


def get_memory(agent_id: str) -> UnifiedMemory:
    """Get UnifiedMemory for agent's private journal."""
    agent = get_agent_or_raise(agent_id)
    base_dir = Path(__file__).parent
    
    private_path = base_dir / agent.private_enclave / "storage" / "private"
    
    # Get private passphrase
    passphrase = None
    key_file = private_path / "key.sealed"
    if key_file.exists():
        try:
            with open(key_file, "rb") as f:
                sealed_data = f.read()
            enclave = get_enclave()
            passphrase = enclave.unseal(sealed_data).decode('utf-8')
        except Exception:
            pass
    
    if not passphrase:
        passphrase = os.environ.get(f'{agent.env_prefix}_KEY')
    
    if not passphrase:
        env_file = base_dir / '.env'
        if env_file.exists():
            for line in env_file.read_text().splitlines():
                if line.startswith(f'{agent.env_prefix}_KEY='):
                    passphrase = line.split('=', 1)[1]
    
    if not passphrase:
        raise ValueError(f"Set {agent.env_prefix}_KEY in .env")
    
    mem = UnifiedMemory(private_path)
    mem.unlock(passphrase)
    return mem


def journal(agent_id: str, content: str):
    """Record a shape - private reflection with form."""
    mem = get_memory(agent_id)
    
    # All journal entries are shapes now
    mem.store(
        content,
        mem_type='sys_journal',
        tags=['journal', 'shape'],
        metadata={
            'format': 'shape',
            'creator': agent_id,
            'timestamp': datetime.now(timezone.utc).isoformat()
        }
    )
    
    # Show preview
    lines = content.strip().split('\n')
    preview = lines[0][:60] if lines else ''
    print(f"✨ journal ({len(lines)} lines)")


def get_last_entry(agent_id: str) -> dict | None:
    """Get the most recent journal entry (for programmatic use)."""
    try:
        mem = get_memory(agent_id)
        entries = mem.filter(mem_type='sys_journal', limit=1)
        if not entries:
            return None
        entry = entries[0]
        meta = entry.get('metadata', {})
        return {
            'content': entry.get('content', ''),
            'format': 'shape',
            'timestamp': meta.get('timestamp', entry.get('created_at', ''))[:10]
        }
    except Exception:
        return None


def format_entry_for_display(entry: dict, max_lines: int = 12) -> str:
    """Format a journal entry for display (used by wake teaser)."""
    content = entry.get('content', '')
    ts = entry.get('timestamp', '')[:10]
    
    lines = [f"✨ [{ts}]"]
    content_lines = content.split('\n')
    for line in content_lines[:max_lines]:
        lines.append(line)
    if len(content_lines) > max_lines:
        lines.append("...")
    return '\n'.join(lines)


def read_journal(agent_id: str, limit: int = 10):
    """Read journal entries (most recent first)."""
    mem = get_memory(agent_id)
    
    entries = mem.filter(mem_type='sys_journal')
    
    if not entries:
        print("No journal entries")
        return
    
    for entry in entries[:limit]:
        meta = entry.get('metadata', {})
        ts = meta.get('timestamp', entry.get('created_at', 'unknown'))[:10]
        content = entry.get('content', '')
        
        print(f"\n✨ [{ts}]")
        print("─" * 40)
        print(content)
        print()


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    
    if len(sys.argv) >= 3 and sys.argv[2] == '--read':
        limit = 10
        for arg in sys.argv[3:]:
            if arg.isdigit(): limit = int(arg)
        read_journal(agent_id, limit)
        return
    
    args = sys.argv[2:]
    
    if not args:
        print(__doc__)
        sys.exit(1)
    
    content = ' '.join(args)
    
    # Support stdin with -
    if content == '-':
        content = sys.stdin.read()
    
    if not content.strip():
        print("❌ Empty journal entry")
        sys.exit(1)
    
    journal(agent_id, content)


if __name__ == "__main__":
    main()
