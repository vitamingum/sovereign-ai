#!/usr/bin/env python3
"""
Initiative CLI - View and manage agent action queues.

Usage:
    py initiative_cli.py <agent> [command] [args...]
    
Commands:
    list        Show pending actions (default)
    approve     Approve an action: approve <action_id>
    cancel      Cancel an action: cancel <action_id>
    stats       Show queue statistics
    
Examples:
    py initiative_cli.py opus
    py initiative_cli.py opus approve act_1234567890
    py initiative_cli.py opus stats
"""

import sys
import os
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.initiative import ActionQueue, ActionStatus


def load_passphrase(agent_id: str) -> str:
    """Load passphrase from environment."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    
    passphrase = os.environ.get(f'{prefix}_KEY') or os.environ.get('SOVEREIGN_PASSPHRASE')
    
    if not passphrase:
        print(f"Error: Set SOVEREIGN_PASSPHRASE or {prefix}_KEY")
        sys.exit(1)
    
    return passphrase


def cmd_list(queue: ActionQueue, args: list):
    """List pending actions."""
    print(queue.format_for_display())
    
    ready = queue.get_ready_actions()
    if ready:
        print(f"\n{len(ready)} action(s) ready to execute (approved with prerequisites met)")


def cmd_approve(queue: ActionQueue, args: list):
    """Approve an action."""
    if not args:
        print("Usage: approve <action_id>")
        return
    
    action_id = args[0]
    if queue.approve_action(action_id):
        print(f"Approved: {action_id}")
    else:
        print(f"Action not found: {action_id}")


def cmd_approve_all(queue: ActionQueue, args: list):
    """Approve all pending actions."""
    pending = queue.get_pending_actions()
    count = 0
    for action in pending:
        if action.status == ActionStatus.PENDING:
            queue.approve_action(action.id)
            count += 1
    print(f"Approved {count} action(s)")


def cmd_cancel(queue: ActionQueue, args: list):
    """Cancel an action."""
    if not args:
        print("Usage: cancel <action_id>")
        return
    
    action_id = args[0]
    if queue.cancel_action(action_id):
        print(f"Cancelled: {action_id}")
    else:
        print(f"Action not found: {action_id}")


def cmd_stats(queue: ActionQueue, args: list):
    """Show queue statistics."""
    stats = queue.get_stats()
    
    print(f"Total actions: {stats['total']}")
    print(f"Pending: {stats['pending_count']} ({stats['pending_tokens']} tokens)")
    print()
    print("By status:")
    for status, count in stats['by_status'].items():
        if count > 0:
            print(f"  {status}: {count}")
    print()
    print("By type:")
    for atype, count in stats['by_type'].items():
        if count > 0:
            print(f"  {atype}: {count}")


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1].lower()
    command = sys.argv[2] if len(sys.argv) > 2 else 'list'
    args = sys.argv[3:]
    
    try:
        agent = get_agent_or_raise(agent_id)
    except ValueError as e:
        print(f"Error: {e}")
        sys.exit(1)
    
    passphrase = load_passphrase(agent_id)
    
    base_dir = Path(__file__).parent
    queue = ActionQueue(base_dir / agent.enclave)
    queue.unlock(passphrase)
    
    commands = {
        'list': cmd_list,
        'approve': cmd_approve,
        'approve-all': cmd_approve_all,
        'cancel': cmd_cancel,
        'stats': cmd_stats,
    }
    
    if command in commands:
        commands[command](queue, args)
    else:
        print(f"Unknown command: {command}")
        print(f"Available: {', '.join(commands.keys())}")
        sys.exit(1)


if __name__ == "__main__":
    main()
