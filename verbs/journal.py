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
sys.path.insert(0, str(Path(__file__).parent.parent))

from lib_enclave import verb_helpers
from lib_enclave.sovereign_agent import SovereignAgent

verb_helpers.safe_init()


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
    parser = verb_helpers.create_parser(
        description='journal — whatever arrives, catch it',
        epilog='''
        whatever arrives
                catch it

        stream is faster than structure
                do not lose the drop

        usage:
                py journal [agent] "content"     | direct
                py journal [agent] @file         | from file
                echo "content" | py journal      | stdin
                py journal --read N              | last N entries
        '''
    )
    # Note: 'agent' interception is handled by parse_args
    # We defines 'content' as our first expected positional.
    parser.add_argument('content', nargs='*', help='Content to journal (or @file)')
    parser.add_argument('--read', type=int, nargs='?', const=5, metavar='N',
                        help='Read last N journal entries (default: 5)')
    
    # Use helper to parse (handles interception)
    args = verb_helpers.parse_args(parser)
    
    # Resolve agent
    try:
        agent_id = verb_helpers.resolve_agent(args)
        agent = SovereignAgent.from_id(agent_id)
    except Exception as e:
        print(f"\n        !error: {e}\n")
        sys.exit(1)
    
    # Read mode
    if args.read is not None:
        print(f"\n        journal as {agent.agent.id}")
        journals = read_journals(agent, limit=args.read)
        render_journals(journals)
        return
    
    # Determine content source - prioritize stdin for AI agents
    content = None
    
    # 1. Check stdin first (piped input from AI)
    if not sys.stdin.isatty():
        content = sys.stdin.read()
    # 2. Then check arguments
    elif args.content:
        # Join all content parts (handles multi-word arguments)
        content_str = ' '.join(args.content)
        
        if content_str.startswith('@'):
            # Try as file first, fall back to literal content
            file_path = content_str[1:]
            if Path(file_path).exists():
                content = read_file_content(file_path)
            else:
                # Treat as literal content (remove @ prefix)
                content = file_path
        else:
            # Direct string (joined)
            content = content_str
    else:
        # 3. No input at all - read mode should have caught this
        print("\n        ∅ no content provided\n")
        print("        usage: echo 'content' | journal OR journal 'content'\n")
        sys.exit(1)
    
    # Guard: empty content
    if not content or not content.strip():
        print("\n        ∅ nothing to hold\n")
        return
    
    # Store it
    line_count = store_journal(agent, content)
    print(f"\n        ⧫ held ({line_count} lines)\n")


if __name__ == '__main__':
    main()

