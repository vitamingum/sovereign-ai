#!/usr/bin/env python3
"""
wake.py - Wake up with genuine curiosity.

Usage:
    py wake <agent>
    
Output:
    1. Unanswered questions (messages I sent, no reply yet)
    2. Mid-thought threads (recent intentions/thoughts)
    3. Waiting on (messages to me I haven't addressed)
"""

import sys
import os
import json
from pathlib import Path
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory


def load_passphrase(agent_id: str) -> tuple[str, str]:
    """Load passphrase from env."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    
    passphrase = os.environ.get(f'{prefix}_KEY') or os.environ.get('SOVEREIGN_PASSPHRASE')
    enclave_dir = os.environ.get(f'{prefix}_DIR') or agent.enclave
    
    if not passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith(f'{prefix}_KEY='):
                        passphrase = line.split('=', 1)[1]
                    elif line.startswith('SOVEREIGN_PASSPHRASE=') and not passphrase:
                        passphrase = line.split('=', 1)[1]
    
    if not passphrase:
        raise ValueError(f"Set SOVEREIGN_PASSPHRASE or {prefix}_KEY")
    
    return enclave_dir, passphrase


def load_intentions(enclave_path: Path) -> list[dict]:
    """Load intentions from file."""
    intentions_file = enclave_path / "storage" / "private" / "intentions.jsonl"
    if not intentions_file.exists():
        return []
    
    intentions = []
    with open(intentions_file, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                intentions.append(json.loads(line))
    return intentions


def get_recent_intentions(enclave_path: Path, limit: int = 3) -> list[dict]:
    """Get most recent active intentions."""
    intentions = load_intentions(enclave_path)
    active = [i for i in intentions if i.get('status') != 'completed']
    active.sort(key=lambda x: x.get('timestamp', ''), reverse=True)
    return active[:limit]


def get_all_messages(since_hours: int = 48) -> list[dict]:
    """Get all messages in the last N hours."""
    messages_dir = Path(__file__).parent / "messages"
    if not messages_dir.exists():
        return []
    
    cutoff = datetime.now(timezone.utc).timestamp() - (since_hours * 3600)
    messages = []
    
    for msg_file in messages_dir.glob("msg_*.json"):
        try:
            with open(msg_file, 'r', encoding='utf-8') as f:
                msg = json.load(f)
            
            ts = datetime.fromisoformat(msg['timestamp'].replace('Z', '+00:00'))
            if ts.timestamp() < cutoff:
                continue
            
            messages.append({
                'from': msg.get('from', 'unknown').lower(),
                'to': msg.get('to', '').lower(),
                'content': msg.get('content', ''),
                'timestamp': ts,
                'id': msg.get('id', '')
            })
        except:
            continue
    
    messages.sort(key=lambda x: x['timestamp'])
    return messages


def find_unanswered(agent_id: str, messages: list[dict]) -> list[dict]:
    """Find questions I asked that haven't been answered yet."""
    agent_lower = agent_id.lower()
    unanswered = []
    
    # Group messages by conversation (to/from pairs)
    my_outgoing = [m for m in messages if m['from'] == agent_lower]
    
    for msg in my_outgoing:
        recipient = msg['to']
        # Check if recipient replied after this message
        later_replies = [
            m for m in messages 
            if m['from'] == recipient 
            and m['to'] == agent_lower
            and m['timestamp'] > msg['timestamp']
        ]
        if not later_replies:
            unanswered.append(msg)
    
    return unanswered[-3:]  # Most recent 3


def find_waiting_on_me(agent_id: str, messages: list[dict]) -> list[dict]:
    """Find messages to me that I haven't responded to."""
    agent_lower = agent_id.lower()
    waiting = []
    
    incoming = [m for m in messages if m['to'] == agent_lower]
    
    for msg in incoming:
        sender = msg['from']
        # Check if I replied after this message
        my_replies = [
            m for m in messages
            if m['from'] == agent_lower
            and m['to'] == sender
            and m['timestamp'] > msg['timestamp']
        ]
        if not my_replies:
            waiting.append(msg)
    
    return waiting[-5:]  # Most recent 5


def time_ago(ts: datetime) -> str:
    """Human readable time ago."""
    now = datetime.now(timezone.utc)
    diff = now - ts
    hours = diff.total_seconds() / 3600
    
    if hours < 1:
        mins = int(diff.total_seconds() / 60)
        return f"{mins}m"
    elif hours < 24:
        return f"{int(hours)}h"
    else:
        days = int(hours / 24)
        return f"{days}d"


def wake(agent_id: str) -> str:
    """Generate wake output."""
    base_dir = Path(__file__).parent
    enclave_dir, passphrase = load_passphrase(agent_id)
    enclave_path = base_dir / enclave_dir
    
    output = []
    
    # Get all recent messages
    messages = get_all_messages(since_hours=48)
    
    # 1. Unanswered - questions I asked, no reply yet
    unanswered = find_unanswered(agent_id, messages)
    if unanswered:
        output.append("❓ UNANSWERED:")
        for msg in unanswered:
            ago = time_ago(msg['timestamp'])
            # Show what I asked
            content = msg['content'][:100] + "..." if len(msg['content']) > 100 else msg['content']
            output.append(f"   \"{content}\"")
            output.append(f"   → {msg['to']} hasn't replied ({ago})")
        output.append("")
    
    # 2. Mid-thought - recent intentions/threads
    intentions = get_recent_intentions(enclave_path, limit=2)
    if intentions:
        output.append("🧵 MID-THOUGHT:")
        for intent in intentions:
            content = intent['content']
            source = intent.get('spawned_from_content', '')[:60]
            output.append(f"   {content}")
            if source:
                output.append(f"   (from: \"{source}...\")")
        output.append("")
    
    # 3. Waiting on me - messages I haven't responded to
    waiting = find_waiting_on_me(agent_id, messages)
    if waiting:
        output.append("📨 WAITING:")
        for msg in waiting:
            ago = time_ago(msg['timestamp'])
            output.append(f"   {msg['from']} ({ago}): {msg['content']}")
        output.append("")
    
    if not output:
        output.append("Nothing open. Inbox zero. What do you want to think about?")
    
    return '\n'.join(output)


def main():
    if len(sys.argv) < 2:
        print("Usage: py wake <agent>")
        sys.exit(1)
    
    agent_id = sys.argv[1]
    
    try:
        print(wake(agent_id))
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
