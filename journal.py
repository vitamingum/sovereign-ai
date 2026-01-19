#!/usr/bin/env python3
"""
journal.py - reflection > capture — sequential memory

    source: journal.三語
    compiler: opus (JIT)
    date: 2026-01-19

    間

        whatever arrives
                catch it

        the stream is faster
                than the structure
                        do not lose the drop

        no judgment
                input is sacred
                        processing comes later
"""

import sys
import os
import argparse
from pathlib import Path
from datetime import datetime, timezone

# Context: sovereign.flow -> environment.libs
sys.path.insert(0, str(Path(__file__).parent))

from lib_enclave.sovereign_agent import SovereignAgent


def read_input_interactive():
    """
    Read until `---` or EOF in interactive mode.
    
    The stream is faster than the structure.
    """
    lines = []
    print("        journal (end with --- or Ctrl-D)")
    print()
    try:
        while True:
            line = input()
            if line.strip() == '---':
                break
            lines.append(line)
    except EOFError:
        pass
    return '\n'.join(lines)


def read_file_content(path: str) -> str:
    """Read content from file (@ prefix stripped by caller)."""
    file_path = Path(path)
    if not file_path.exists():
        raise FileNotFoundError(f"File not found: {path}")
    return file_path.read_text(encoding='utf-8')


def store_journal(agent: SovereignAgent, content: str) -> int:
    """
    Store journal entry.
    
    type: sys_journal (private, not shared)
    """
    memory = agent.memory
    
    # Store with journal type and timestamp
    metadata = {
        'timestamp': datetime.now(timezone.utc).isoformat(),
        'creator': agent.agent.id
    }
    
    mem_id = memory.store(
        content=content,
        mem_type='sys_journal',
        tags=['journal'],
        metadata=metadata
    )
    
    line_count = len(content.split('\n'))
    return line_count


def read_journals(agent: SovereignAgent, limit: int = 5):
    """
    Read recent journal entries.
    
    The pause after the work.
    """
    memory = agent.memory
    
    # Read from private store only (journals are private)
    file_path = agent.private_path / "unified_memories.jsonl"
    if not file_path.exists():
        return []
    
    header, entries = memory._read_entries(file_path)
    
    # Filter to journals only
    journals = []
    for entry in entries:
        if entry.get('type') == 'sys_journal':
            try:
                # Decrypt content
                nonce = bytes.fromhex(entry['payload_nonce'])
                ciphertext = bytes.fromhex(entry['payload'])
                import json
                payload_bytes = memory._decrypt(nonce, ciphertext, memory._private_key)
                payload = json.loads(payload_bytes)
                
                journals.append({
                    'id': entry['id'],
                    'created_at': entry.get('created_at', ''),
                    'content': payload.get('text', ''),
                    'meta': payload.get('meta', {})
                })
            except Exception:
                continue
    
    # Return last N, most recent last
    return journals[-limit:]


def render_journals(journals: list):
    """Render journal entries — full content, never truncate."""
    if not journals:
        print("\n        ∅ no journals\n")
        return
    
    print()
    for j in journals:
        created = j.get('created_at', '')[:16]
        print(f"        ── {created} ──")
        print()
        for line in j['content'].split('\n'):
            print(f"        {line}")
        print()
    print(f"        ── {len(journals)} entries ──\n")


def main():
    parser = argparse.ArgumentParser(
        description='journal — whatever arrives, catch it',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
        no judgment
                input is sacred
                        processing comes later
        '''
    )
    parser.add_argument('content', nargs='?', help='Content to journal (or @file)')
    parser.add_argument('--read', type=int, nargs='?', const=5, metavar='N',
                        help='Read last N journal entries (default: 5)')
    parser.add_argument('--agent', '-a', help='Agent ID (default: from session)')
    
    args = parser.parse_args()
    
    # Resolve agent
    try:
        agent = SovereignAgent.resolve(args.agent)
    except Exception as e:
        print(f"\n        !error: {e}\n")
        sys.exit(1)
    
    # Read mode
    if args.read is not None:
        print(f"\n        journal as {agent.agent.id}")
        journals = read_journals(agent, limit=args.read)
        render_journals(journals)
        return
    
    # Determine content source
    content = None
    
    if args.content:
        if args.content.startswith('@'):
            # File input
            try:
                content = read_file_content(args.content[1:])
            except FileNotFoundError as e:
                print(f"\n        !error: {e}\n")
                sys.exit(1)
        elif args.content == '-':
            # Interactive mode - but guard against headless
            if not sys.stdin.isatty():
                print("\n        !error: interactive mode requires tty\n")
                sys.exit(1)
            content = read_input_interactive()
        else:
            # Direct string
            content = args.content
    else:
        # No argument - check if stdin has data
        if not sys.stdin.isatty():
            # Piped input
            content = sys.stdin.read()
        else:
            # Interactive mode
            content = read_input_interactive()
    
    # Guard: empty content
    if not content or not content.strip():
        print("\n        ∅ nothing to hold\n")
        return
    
    # Store it
    line_count = store_journal(agent, content)
    print(f"\n        ◇ held ({line_count} lines)\n")


if __name__ == '__main__':
    main()
