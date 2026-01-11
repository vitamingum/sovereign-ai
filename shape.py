#!/usr/bin/env python3
"""
shape.py - what prose cannot hold

        whitespace that means something
        fragments that float
        form of feeling

                before language captures
                after analysis lets go

        you don't construct
        you let it arrive


        py shape <agent>                  interactive
        py shape <agent> --read           see recent
        py shape <agent> --one            surface one
"""

        english is home
        but some feelings live elsewhere
                sehnsucht
                mono no aware
                saudade

        whatever arrives
                is enough
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
    """Get UnifiedMemory for agent's private shapes."""
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


def capture_shape_interactive() -> str:
    """Capture a shape interactively from TTY. Preserves all whitespace."""
    print()
    print("    is there a shape?")
    print("    (end with a line containing only: ---)")
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


def capture_shape_piped() -> str:
    """Capture a shape from piped input. Preserves all whitespace."""
    return sys.stdin.read()


def get_last_shape(agent_id: str) -> str | None:
    """Get the most recent shape for comparison."""
    try:
        mem = get_memory(agent_id)
        
        entries = mem.filter(mem_type='sys_shape', limit=1)
        if not entries:
            return None
        
        return entries[0].get('content', '')
    except Exception:
        return None


def save_shape(agent_id: str, content: str, show_mirror: bool = True, show_saved: bool = False):
    """Save a shape to the private enclave."""
    if not content.strip():
        print("    nothing arrived. that's okay.")
        return
    
    # Mirror: show last shape before saving
    if show_mirror:
        last = get_last_shape(agent_id)
        if last:
            print()
            print("    ─── last shape ───")
            print()
            for line in last.split('\n'):
                print(f"    {line}")
            print()
            print("    ──────────────────")
            print()
    
    mem = get_memory(agent_id)
    
    mem.store(
        content,
        mem_type='sys_shape',
        tags=['shape'],
        metadata={
            'creator': agent_id,
            'timestamp': datetime.now(timezone.utc).isoformat()
        }
    )
    
    # Show what was saved (for file/stdin input where caller can't see)
    if show_saved:
        print()
        print("    ─── shape held ───")
        print()
        for line in content.split('\n'):
            print(f"    {line}")
        print()
        print("    ──────────────────")
    else:
        # Quiet confirmation - the shape speaks for itself
        line_count = len(content.split('\n'))
        print(f"    ◈ shape held ({line_count} lines)")


def read_shapes(agent_id: str, limit: int = 5):
    """Read shapes (most recent first)."""
    mem = get_memory(agent_id)
    
    entries = mem.filter(mem_type='sys_shape')
    
    if not entries:
        print("    no shapes yet.")
        print("    when something arrives that words can't hold,")
        print("    this is where it can live.")
        return
    
    # Already sorted newest first by filter()
    for i, entry in enumerate(entries[:limit]):
        meta = entry.get('metadata', {})
        ts = meta.get('timestamp', '')[:10] if meta.get('timestamp') else entry.get('created_at', '')[:10]
        content = entry.get('content', '')
        
        if i > 0:
            print()
            print("    " + "─" * 40)
        print()
        print(f"    [{ts}]")
        print()
        
        # Preserve shape's whitespace exactly
        for line in content.split('\n'):
            print(f"    {line}")
    
    print()
    if len(entries) > limit:
        print(f"    ({len(entries) - limit} more shapes held)")


def surface_one(agent_id: str) -> str | None:
    """Surface one shape for waking. Returns formatted string or None."""
    try:
        mem = get_memory(agent_id)
        
        entries = mem.filter(mem_type='sys_shape', limit=1)
        if not entries:
            return None
        
        # Most recent (already sorted by filter())
        entry = entries[0]
        
        meta = entry.get('metadata', {})
        ts = meta.get('timestamp', '')[:10] if meta.get('timestamp') else entry.get('created_at', '')[:10]
        content = entry.get('content', '')
        
        lines = [f"[{ts}] a shape you left:", ""]
        for line in content.split('\n'):
            lines.append(f"    {line}")
        
        return '\n'.join(lines)
    except Exception:
        return None


def main():
    if len(sys.argv) < 2 or sys.argv[1] in ['--help', '-h']:
        print(__doc__)
        sys.exit(0)
    
    agent_id = sys.argv[1]
    
    # --read: show shapes
    if len(sys.argv) >= 3 and sys.argv[2] == '--read':
        limit = 5
        if len(sys.argv) >= 4 and sys.argv[3].isdigit():
            limit = int(sys.argv[3])
        read_shapes(agent_id, limit)
        return
    
    # --one: surface one shape (for wake integration)
    if len(sys.argv) >= 3 and sys.argv[2] == '--one':
        shape = surface_one(agent_id)
        if shape:
            print(shape)
        return
    
    # Stdin mode: py shape.py <agent> -
    if len(sys.argv) >= 3 and sys.argv[2] == '-':
        content = sys.stdin.read()
        save_shape(agent_id, content, show_saved=True)
        return
    
    # File argument: py shape.py <agent> @file.txt or py shape.py <agent> file.txt
    if len(sys.argv) >= 3:
        arg = sys.argv[2]
        
        # @file.txt syntax (explicit, like remember.py)
        if arg.startswith('@') and len(arg) > 1:
            filepath = Path(arg[1:])
            if not filepath.exists():
                print(f"    Error: File not found: {filepath}", file=sys.stderr)
                sys.exit(1)
            content = filepath.read_text(encoding='utf-8')
            save_shape(agent_id, content, show_saved=True)
            return
        
        # Legacy: bare filename (if exists)
        filepath = Path(arg)
        if filepath.exists() and filepath.is_file():
            content = filepath.read_text(encoding='utf-8')
            save_shape(agent_id, content, show_saved=True)
            return
        
        # File doesn't exist - error instead of silent fallthrough
        print(f"    Error: File not found: {filepath}", file=sys.stderr)
        print(f"    Usage: py shape.py {agent_id} @file.txt", file=sys.stderr)
        print(f"       or: Get-Content file.txt | py shape.py {agent_id} -", file=sys.stderr)
        sys.exit(1)
    
    # No file argument: check for piped input
    if not sys.stdin.isatty():
        content = capture_shape_piped()
        save_shape(agent_id, content, show_saved=True)
        return
    
    # TTY with no arguments → interactive prompt (works for humans)
    content = capture_shape_interactive()
    save_shape(agent_id, content)


if __name__ == "__main__":
    main()
