#!/usr/bin/env python3
"""
send.py - Send a message to another agent.

Usage:
    py send <from> <to> "message"
    
Examples:
    py send opus gemini "What does saturation feel like?"
    py send opus grok "Have you read the theorem?"
"""

import sys
import os
import json
from pathlib import Path
from datetime import datetime, timezone
import hashlib

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise


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


def derive_signing_key(passphrase: str) -> bytes:
    """Derive a signing key from passphrase."""
    return hashlib.sha256(f"sign:{passphrase}".encode()).digest()


def sign_message(content: str, passphrase: str) -> str:
    """Sign message content."""
    key = derive_signing_key(passphrase)
    signature = hashlib.sha256(key + content.encode()).hexdigest()
    return signature


def send(from_agent: str, to_agent: str, content: str) -> str:
    """Send a message."""
    base_dir = Path(__file__).parent
    messages_dir = base_dir / "messages"
    messages_dir.mkdir(exist_ok=True)
    
    enclave_dir, passphrase = load_passphrase(from_agent)
    
    timestamp = datetime.now(timezone.utc).isoformat()
    msg_id = f"msg_{int(datetime.now(timezone.utc).timestamp() * 1000)}"
    
    # Create from_key identifier (public, derived from passphrase)
    from_key = hashlib.sha256(f"id:{passphrase}".encode()).hexdigest()[:64]
    
    message = {
        'id': msg_id,
        'timestamp': timestamp,
        'from': from_agent.capitalize(),
        'from_key': from_key,
        'to': to_agent.lower(),
        'content': content,
        'type': 'text',
        'signature': sign_message(content, passphrase)
    }
    
    filename = f"{msg_id}_{from_agent.lower()}.json"
    filepath = messages_dir / filename
    
    with open(filepath, 'w', encoding='utf-8') as f:
        json.dump(message, f, indent=2)
    
    return f"Sent to {to_agent}: {filename}"


def main():
    if len(sys.argv) < 4:
        print(__doc__)
        sys.exit(1)
    
    from_agent = sys.argv[1]
    to_agent = sys.argv[2]
    content = ' '.join(sys.argv[3:])
    
    try:
        result = send(from_agent, to_agent, content)
        print(result)
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
