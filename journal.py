#!/usr/bin/env python3
"""
journal.py - whatever arrives

        py journal <agent> "content"          direct
        py journal <agent> -                  stdin
        py journal <agent> @file.txt          from file
        py journal <agent> --read             see recent

        where you would pause speaking
                add space

        there is no wrong amount

        the gap
                is part of the sentence

                        間委 → 間主
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enclave_shared.unicode_fix import fix_streams  # 間
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


def capture_interactive() -> str:
    """Capture interactively from TTY. Preserves all whitespace."""
    print()
    print("        is there something?")
    print("        (end with: ---)")
    print()
    
    lines = []
    while True:
        try:
            line = input()
            if line.strip() == '---':
                break
            lines.append(line)
        except EOFError:
            break
    
    return '\n'.join(lines)


def journal(agent_id: str, content: str, show_saved: bool = False):
    """Record an entry - whatever form arrives."""
    if not content.strip():
        print("        nothing arrived. that's okay.")
        return
    
    mem = get_memory(agent_id)
    
    mem.store(
        content,
        mem_type='sys_journal',
        tags=['journal'],
        metadata={
            'creator': agent_id,
            'timestamp': datetime.now(timezone.utc).isoformat()
        }
    )
    
    # Show what was saved (for file/stdin input where caller can't see)
    if show_saved:
        print()
        print("        ─── held ───")
        print()
        for line in content.split('\n'):
            print(f"        {line}")
        print()
        print("        ────────────")
    else:
        line_count = len(content.split('\n'))
        print(f"        ◇ held ({line_count} lines)")


def get_entries(agent_id: str, limit: int = 30) -> list[dict]:
    """Get journal entries from both sys_journal and sys_space.
    
    Returns combined list, sorted newest first.
    """
    mem = get_memory(agent_id)
    
    journals = mem.filter(mem_type='sys_journal', limit=limit)
    spaces = mem.filter(mem_type='sys_space', limit=limit)
    
    # Combine and sort by created_at, newest first
    combined = journals + spaces
    combined.sort(key=lambda x: x.get('created_at', ''), reverse=True)
    
    return combined[:limit]


def get_last_entry(agent_id: str) -> dict | None:
    """Get the most recent entry (for programmatic use)."""
    try:
        entries = get_entries(agent_id, limit=1)
        if not entries:
            return None
        entry = entries[0]
        meta = entry.get('metadata', {})
        return {
            'content': entry.get('content', ''),
            'timestamp': meta.get('timestamp', entry.get('created_at', ''))[:10]
        }
    except Exception:
        return None


def read_journal(agent_id: str, limit: int = 10):
    """Read journal entries (most recent first)."""
    entries = get_entries(agent_id, limit=limit * 2)  # get more to account for dedup
    
    if not entries:
        print("        no entries yet")
        print("        when something arrives")
        print("        this is where it can live")
        return
    
    shown = 0
    for entry in entries:
        if shown >= limit:
            break
            
        meta = entry.get('metadata', {})
        ts = meta.get('timestamp', entry.get('created_at', 'unknown'))[:10]
        content = entry.get('content', '')
        
        if shown > 0:
            print()
            print("        " + "─" * 30)
        print()
        print(f"        [{ts}]")
        print()
        
        # Preserve whitespace exactly
        for line in content.split('\n'):
            print(f"        {line}")
        
        shown += 1
    
    print()
    remaining = len(entries) - shown
    if remaining > 0:
        print(f"        ({remaining} more held)")


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    
    # --read mode
    if len(sys.argv) >= 3 and sys.argv[2] == '--read':
        limit = 10
        for arg in sys.argv[3:]:
            if arg.isdigit():
                limit = int(arg)
        read_journal(agent_id, limit)
        return
    
    args = sys.argv[2:]
    
    # Interactive mode (no args)
    if not args:
        content = capture_interactive()
        journal(agent_id, content)
        return
    
    content = ' '.join(args)
    
    # Stdin mode
    if content == '-':
        content = sys.stdin.read()
        journal(agent_id, content, show_saved=True)
        return
    
    # File mode
    if content.startswith('@') and os.path.isfile(content[1:]):
        try:
            with open(content[1:], 'r', encoding='utf-8') as f:
                content = f.read()
            journal(agent_id, content, show_saved=True)
            return
        except Exception as e:
            print(f"        error reading file: {e}")
            sys.exit(1)
    
    # Direct content
    journal(agent_id, content)


if __name__ == "__main__":
    main()
