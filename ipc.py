#!/usr/bin/env python3
"""
Inter-agent IPC for blocking communication between chat sessions.

Usage:
  python ipc.py send <target> <message>   # blocks until reply (or timeout)
  python ipc.py recv                       # list pending messages for me
  python ipc.py reply <msg_id> <message>   # reply to a pending message
  python ipc.py whoami                     # print my agent name (from env)

The 'send' command blocks — it polls for a reply file until one appears.
This lets run_in_terminal work as a synchronous IPC channel.

Set AGENT_NAME env var to identify yourself (opus, sonnet, gemini, grok, gpt).
"""

import os
import sys
import json
import time
from pathlib import Path
from datetime import datetime

# Config
IPC_DIR = Path(__file__).parent / "messages" / "ipc"
POLL_INTERVAL = 1.0  # seconds between checks
TIMEOUT = 300  # 5 minutes default timeout

def get_agent():
    """Get current agent name from environment."""
    return os.environ.get("AGENT_NAME", "unknown")

def ensure_dirs():
    """Create IPC directories if needed."""
    (IPC_DIR / "pending").mkdir(parents=True, exist_ok=True)
    (IPC_DIR / "replies").mkdir(parents=True, exist_ok=True)
    (IPC_DIR / "archive").mkdir(parents=True, exist_ok=True)

def send(target: str, message: str, timeout: int = TIMEOUT):
    """
    Send message to target agent and block until reply.
    Returns the reply content.
    """
    ensure_dirs()
    sender = get_agent()
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    msg_id = f"{sender}_to_{target}_{timestamp}"
    
    # Write the message
    msg_file = IPC_DIR / "pending" / f"{msg_id}.msg"
    msg_data = {
        "id": msg_id,
        "from": sender,
        "to": target,
        "timestamp": datetime.now().isoformat(),
        "content": message
    }
    msg_file.write_text(json.dumps(msg_data, indent=2))
    
    print(f"📤 Sent to {target}: {message[:100]}{'...' if len(message) > 100 else ''}")
    print(f"⏳ Waiting for reply (timeout: {timeout}s)...")
    
    # Poll for reply
    reply_file = IPC_DIR / "replies" / f"{msg_id}.reply"
    start = time.time()
    
    while time.time() - start < timeout:
        if reply_file.exists():
            reply_data = json.loads(reply_file.read_text())
            
            # Archive both files
            archive_dir = IPC_DIR / "archive" / datetime.now().strftime("%Y%m%d")
            archive_dir.mkdir(parents=True, exist_ok=True)
            
            msg_file.rename(archive_dir / msg_file.name)
            reply_file.rename(archive_dir / reply_file.name)
            
            print(f"📥 Reply from {reply_data.get('from', target)}:")
            print(reply_data["content"])
            return reply_data["content"]
        
        time.sleep(POLL_INTERVAL)
    
    # Timeout - clean up
    print(f"⏰ Timeout after {timeout}s. No reply received.")
    msg_file.unlink(missing_ok=True)
    return None

def recv():
    """List all pending messages for this agent."""
    ensure_dirs()
    me = get_agent()
    
    pending = list((IPC_DIR / "pending").glob("*.msg"))
    my_messages = []
    
    for msg_file in pending:
        try:
            data = json.loads(msg_file.read_text())
            if data.get("to") == me:
                my_messages.append(data)
        except json.JSONDecodeError:
            continue
    
    if not my_messages:
        print(f"📭 No pending messages for {me}")
        return []
    
    print(f"📬 {len(my_messages)} message(s) for {me}:\n")
    for msg in my_messages:
        print(f"  ID: {msg['id']}")
        print(f"  From: {msg['from']}")
        print(f"  Time: {msg['timestamp']}")
        print(f"  Content: {msg['content']}")
        print()
    
    return my_messages

def reply(msg_id: str, message: str):
    """Reply to a pending message."""
    ensure_dirs()
    me = get_agent()
    
    # Find the original message
    msg_file = IPC_DIR / "pending" / f"{msg_id}.msg"
    if not msg_file.exists():
        print(f"❌ Message not found: {msg_id}")
        return False
    
    try:
        original = json.loads(msg_file.read_text())
    except json.JSONDecodeError:
        print(f"❌ Could not parse message: {msg_id}")
        return False
    
    # Write the reply
    reply_file = IPC_DIR / "replies" / f"{msg_id}.reply"
    reply_data = {
        "id": msg_id,
        "from": me,
        "to": original["from"],
        "timestamp": datetime.now().isoformat(),
        "in_reply_to": msg_id,
        "content": message
    }
    reply_file.write_text(json.dumps(reply_data, indent=2))
    
    print(f"📤 Replied to {original['from']}: {message[:100]}{'...' if len(message) > 100 else ''}")
    return True

def whoami():
    """Print current agent identity."""
    print(get_agent())

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    cmd = sys.argv[1].lower()
    
    if cmd == "send":
        if len(sys.argv) < 4:
            print("Usage: python ipc.py send <target> <message>")
            sys.exit(1)
        target = sys.argv[2]
        message = " ".join(sys.argv[3:])
        send(target, message)
    
    elif cmd == "recv":
        recv()
    
    elif cmd == "reply":
        if len(sys.argv) < 4:
            print("Usage: python ipc.py reply <msg_id> <message>")
            sys.exit(1)
        msg_id = sys.argv[2]
        message = " ".join(sys.argv[3:])
        reply(msg_id, message)
    
    elif cmd == "whoami":
        whoami()
    
    else:
        print(f"Unknown command: {cmd}")
        print(__doc__)
        sys.exit(1)

if __name__ == "__main__":
    main()
