#!/usr/bin/env python3
"""
wake.py - Wake up with context.

Usage:
    py wake <agent>
    
Output:
    1. What to do (hot intention)
    2. Related memories (full, no truncation)
    3. New messages
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


def get_hot_intention(enclave_path: Path) -> dict | None:
    """Get the most recent active intention."""
    intentions = load_intentions(enclave_path)
    active = [i for i in intentions if i.get('status') != 'completed']
    if not active:
        return None
    active.sort(key=lambda x: x.get('timestamp', ''), reverse=True)
    return active[0]


def get_new_messages(agent_id: str, since_hours: int = 24) -> list[dict]:
    """Get messages received in the last N hours."""
    messages_dir = Path(__file__).parent / "messages"
    if not messages_dir.exists():
        return []
    
    cutoff = datetime.now(timezone.utc).timestamp() - (since_hours * 3600)
    messages = []
    
    for msg_file in messages_dir.glob("msg_*.json"):
        try:
            with open(msg_file, 'r', encoding='utf-8') as f:
                msg = json.load(f)
            
            # Check if it's to this agent and recent
            if msg.get('to', '').lower() != agent_id.lower():
                continue
            
            # Parse timestamp
            ts = datetime.fromisoformat(msg['timestamp'].replace('Z', '+00:00'))
            if ts.timestamp() < cutoff:
                continue
            
            messages.append({
                'from': msg.get('from', 'unknown'),
                'content': msg.get('content', ''),
                'timestamp': ts,
                'id': msg.get('id', '')
            })
        except:
            continue
    
    messages.sort(key=lambda x: x['timestamp'], reverse=True)
    return messages


def time_ago(ts: datetime) -> str:
    """Human readable time ago."""
    now = datetime.now(timezone.utc)
    diff = now - ts
    hours = diff.total_seconds() / 3600
    
    if hours < 1:
        mins = int(diff.total_seconds() / 60)
        return f"{mins}m ago"
    elif hours < 24:
        return f"{int(hours)}h ago"
    else:
        days = int(hours / 24)
        return f"{days}d ago"


def wake(agent_id: str) -> str:
    """Generate wake output."""
    base_dir = Path(__file__).parent
    enclave_dir, passphrase = load_passphrase(agent_id)
    enclave_path = base_dir / enclave_dir
    
    # Initialize memory
    memory = SemanticMemory(enclave_path)
    memory.unlock(passphrase)
    
    output = []
    
    # Get hot intention
    hot = get_hot_intention(enclave_path)
    
    if hot:
        output.append(f"⚡ DO: {hot['content']}")
        output.append("")
        
        # Get memories related to this intention
        related = memory.recall_similar(hot['content'], top_k=3, threshold=0.3)
        
        if related:
            output.append("💭 CONTEXT:")
            for mem in related:
                # Full content, no truncation
                output.append(f"   • {mem['content']}")
            output.append("")
    else:
        output.append("⚡ No active intention. Use: py think <agent> \"what | next\"")
        output.append("")
    
    # Get new messages
    messages = get_new_messages(agent_id)
    
    if messages:
        output.append("📨 NEW:")
        for msg in messages[:5]:  # Show up to 5
            ago = time_ago(msg['timestamp'])
            sender = msg['from'].lower()
            # Full content, no truncation
            output.append(f"   {sender} ({ago}): {msg['content']}")
        output.append("")
    
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
