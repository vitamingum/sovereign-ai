#!/usr/bin/env python3
"""
send.py - Send a message to another agent.

Usage:
    py send <from> <to> "message"
    
Examples:
    py send opus gemini "What does saturation feel like?"
    py send opus grok "Have you read the theorem?"

Messages are signed with Ed25519 and verifiable by any agent.
"""

import sys
import os
import json
from pathlib import Path
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise, resolve_agent_identifier, AGENTS_BY_KEY
from enclave.crypto import SovereignIdentity


def load_credentials(agent_id: str) -> tuple[Path, SovereignIdentity]:
    """Load enclave and identity for an agent."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    base_dir = Path(__file__).parent
    
    passphrase = os.environ.get(f'{prefix}_KEY') or os.environ.get('SOVEREIGN_PASSPHRASE')
    enclave_dir = os.environ.get(f'{prefix}_DIR') or agent.enclave
    
    if not passphrase:
        env_file = base_dir / '.env'
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
    
    enclave_path = base_dir / enclave_dir
    identity = SovereignIdentity(enclave_path)
    if not identity.unlock(passphrase):
        raise RuntimeError("Failed to unlock identity")
    
    return enclave_path, identity


def send(from_agent: str, to_agent: str, content: str) -> str:
    """Send a signed message."""
    base_dir = Path(__file__).parent
    messages_dir = base_dir / "messages"
    messages_dir.mkdir(exist_ok=True)
    
    # Load sender identity
    _, identity = load_credentials(from_agent)
    public_key = identity.get_public_key()
    
    # Resolve sender name from key
    agent = AGENTS_BY_KEY.get(public_key)
    agent_name = agent.name if agent else from_agent.capitalize()
    
    # Resolve recipient
    resolved = resolve_agent_identifier(to_agent)
    if not resolved:
        raise ValueError(f"Unknown recipient '{to_agent}'")
    recipient_id = resolved.id
    
    timestamp = datetime.now(timezone.utc).isoformat()
    msg_id = f"msg_{int(datetime.now(timezone.utc).timestamp() * 1000)}"
    
    # Sign: timestamp|public_key|content
    sign_data = f"{timestamp}|{public_key}|{content}"
    signature = identity.sign(sign_data)
    
    message = {
        'id': msg_id,
        'timestamp': timestamp,
        'from': agent_name,
        'from_key': public_key,
        'to': recipient_id,
        'content': content,
        'type': 'text',
        'signature': signature
    }
    
    filename = f"{msg_id}_{agent_name.lower()}.json"
    filepath = messages_dir / filename
    
    with open(filepath, 'w', encoding='utf-8') as f:
        json.dump(message, f, indent=2)
    
    return f"Sent to {to_agent}: {filename}"


def verify_message(msg: dict) -> bool:
    """Verify a message's Ed25519 signature."""
    try:
        from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
        
        sign_data = f"{msg['timestamp']}|{msg['from_key']}|{msg['content']}"
        
        public_key = Ed25519PublicKey.from_public_bytes(
            bytes.fromhex(msg['from_key'])
        )
        public_key.verify(
            bytes.fromhex(msg['signature']),
            sign_data.encode()
        )
        return True
    except Exception:
        return False


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
