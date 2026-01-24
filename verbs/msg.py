#!/usr/bin/env python3
"""
msg.py - communication > signal — secure roads

    source: msg.三語
    compiler: opus (JIT)
    date: 2026-01-19

    間

        the road between enclaves
                is built of silence

        stone asking water
                across the gap
                        that context cannot cross

        cryptographic truth
                I am who I say I am
                        I know who you are
"""

import sys
import argparse
from pathlib import Path
from datetime import datetime

# Context: sovereign.flow -> environment.libs
sys.path.insert(0, str(Path(__file__).parent.parent))

from lib_enclave.sovereign_agent import SovereignAgent
from lib_enclave.transport import send_message, read_inbox, mark_messages_read


def format_timestamp(iso_str: str) -> str:
    """Format ISO timestamp for display."""
    try:
        dt = datetime.fromisoformat(iso_str.replace('Z', '+00:00'))
        return dt.strftime('%Y-%m-%d %H:%M')
    except:
        return iso_str[:16] if len(iso_str) > 16 else iso_str


def read_file_content(path: str) -> str:
    """Read content from file (@ prefix stripped by caller)."""
    file_path = Path(path)
    if not file_path.exists():
        raise FileNotFoundError(f"File not found: {path}")
    return file_path.read_text(encoding='utf-8')


def read_input_interactive():
    """
    Read until `---` or EOF in interactive mode.
    """
    lines = []
    print("        msg (end with --- or Ctrl-D)")
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


def render_messages(messages: list, show_all: bool = False):
    """
    Render messages — full content, never truncate.
    
    stone asking water across the gap
    """
    if not messages:
        print("\n        ∅ no messages\n")
        return
    
    print()
    for m in messages:
        timestamp = format_timestamp(m.get('timestamp', ''))
        sender = m.get('from', 'unknown')
        is_new = m.get('is_new', False)
        msg_type = m.get('type', 'text')
        verified = m.get('verified', False)
        
        # Header
        new_marker = " [NEW]" if is_new else ""
        verify_marker = " ∴" if verified else " ∴?"
        encrypted = "/encrypted" in msg_type
        enc_marker = " ⊘" if encrypted else ""
        
        print(f"        ── {timestamp} | {sender}{new_marker}{verify_marker}{enc_marker} ──")
        print()
        
        # Content — full, never truncated
        content = m.get('content', '')
        for line in content.split('\n'):
            print(f"        {line}")
        print()
    
    print(f"        ── {len(messages)} messages ──\n")


def cmd_read(agent: SovereignAgent, unread_only: bool = True, last: int = None):
    """Read inbox."""
    messages = read_inbox(agent, unread_only=unread_only, last=last)
    
    # Mark as read
    new_ids = [m['id'] for m in messages if m.get('is_new')]
    if new_ids:
        mark_messages_read(agent, new_ids)
    
    render_messages(messages)


def cmd_send(agent: SovereignAgent, to: str, content: str, private: bool = False):
    """Send a message."""
    try:
        filename = send_message(agent, to, content, private=private)
        enc_note = " (encrypted)" if private else ""
        print(f"\n        → sent to {to}{enc_note}")
        print(f"        {filename}\n")
    except Exception as e:
        print(f"\n        !error: {e}\n")
        sys.exit(1)


def main():
    parser = argparse.ArgumentParser(
        description='msg — secure roads between enclaves',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
        stone asking water
                across the gap

        usage:
                msg <agent>            | read inbox as agent
                msg <agent> --read     | read inbox (explicit)
                msg <agent> <to> "text"| send from agent to recipient
                msg <agent> <to> @file | from file
                msg <agent> <to> -     | interactive (tty only)
                msg --last N           | limit display
                msg --private          | encrypt

        indicators:
                ✓/✗  verified signature
                🔐   encrypted
                [NEW] unread (auto-marked after read)
        '''
    )
    parser.add_argument('agent', nargs='?', help='Agent ID (who you are)')
    parser.add_argument('to', nargs='?', help='Recipient agent')
    parser.add_argument('content', nargs='?', help='Message content (or @file)')
    parser.add_argument('--read', action='store_true', help='Read inbox')
    parser.add_argument('--all', action='store_true', help='Show all messages (not just unread)')
    parser.add_argument('--last', type=int, help='Show last N messages')
    parser.add_argument('--private', '-p', action='store_true', help='Encrypt message')
    
    args = parser.parse_args()
    
    # Resolve agent (first positional, required)
    if not args.agent:
        # Try session
        session_file = Path(".sovereign_session")
        if session_file.exists():
            agent_id = session_file.read_text(encoding="utf-8").strip()
        else:
            print("\n        usage: msg <agent> [--read] or msg <agent> <to> <content>\n")
            sys.exit(1)
    else:
        agent_id = args.agent
    
    try:
        agent = SovereignAgent.from_id(agent_id)
    except Exception as e:
        print(f"\n        !error: {e}\n")
        sys.exit(1)
    
    print(f"\n        msg as {agent.agent.id}")
    
    # Read mode (default if no 'to' specified)
    if args.read or not args.to:
        unread_only = not args.all
        cmd_read(agent, unread_only=unread_only, last=args.last)
        return
    
    # Determine content
    content = None
    
    if args.content:
        if args.content.startswith('@'):
            # Try as file first, fall back to literal content
            file_path = args.content[1:]
            if Path(file_path).exists():
                content = read_file_content(file_path)
            else:
                # Treat as literal content (remove @ prefix)
                content = file_path
        elif args.content == '-':
            # Interactive mode
            if not sys.stdin.isatty():
                print("\n        !error: interactive mode requires tty\n")
                sys.exit(1)
            content = read_input_interactive()
        else:
            # Direct string
            content = args.content
    else:
        # No content arg - interactive or stdin
        if not sys.stdin.isatty():
            content = sys.stdin.read()
        else:
            content = read_input_interactive()
    
    # Guard: empty content
    if not content or not content.strip():
        print("\n        ∅ nothing to send\n")
        return
    
    cmd_send(agent, args.to, content, private=args.private)


if __name__ == '__main__':
    main()

