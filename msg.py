#!/usr/bin/env python3
"""
msg.py - Send a message to another agent.

Usage:
    py msg <from> <to> "content"              # Public (unencrypted, signed)
    py msg <from> <to> --private "content"    # Private (encrypted, signed)
    
Examples:
    py msg opus gemini "What does saturation feel like?"
    py msg opus gemini --private "Secret coordination plan"
    py msg opus gemini "@G question opus 2025-12-31; N Q 'What is saturation?'"

Public messages: Signed but unencrypted - any agent can read.
Private messages: Encrypted to recipient's key - only they can decrypt.
All messages are signed with Ed25519 and verifiable by any agent.
"""

import sys
import os
import json
from pathlib import Path
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise, resolve_agent_identifier, AGENTS_BY_KEY
from enclave.crypto import SovereignIdentity
from enclave.sif_parser import SIFParser
from enclave.opaque import OpaqueStorage


def load_credentials(agent_id: str) -> tuple[Path, SovereignIdentity]:
    """Load identity from PRIVATE enclave for signing messages."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    base_dir = Path(__file__).parent
    
    # Private enclave for identity - no fallback
    enclave_dir = agent.private_enclave
    
    # Try private key - no fallback
    passphrase = os.environ.get(f'{prefix}_KEY')
    
    if not passphrase:
        env_file = base_dir / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith(f'{prefix}_KEY='):
                        passphrase = line.split('=', 1)[1]
    
    if not passphrase:
        raise ValueError(f"No passphrase found. Set {prefix}_KEY in .env")
    
    enclave_path = base_dir / enclave_dir
    identity = SovereignIdentity(enclave_path)
    if not identity.unlock(passphrase):
        raise RuntimeError("Failed to unlock identity")
    
    return enclave_path, identity


def send(from_agent: str, to_agent: str, content: str, private: bool = False) -> str:
    """Send a signed message. If private=True, encrypt to recipient."""
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
    
    # Determine content type - detect SIF, Flow, or plain text
    msg_type = 'text'
    final_content = content
    
    # Check if it's SIF format (starts with @G or has SIF structure)
    is_sif = False
    is_flow = False
    if content.strip().startswith('@G'):
        try:
            SIFParser.parse(content)
            is_sif = True
        except ValueError:
            pass  # Not valid SIF, treat as plain text
    elif content.strip().startswith('@F '):
        # Flow format - validate basic structure
        try:
            from enclave.flow_parser import FlowParser
            FlowParser.parse(content)
            is_flow = True
        except (ValueError, ImportError):
            pass  # Not valid Flow, treat as plain text
    
    if is_sif:
        msg_type = 'protocol/sif'
    elif is_flow:
        msg_type = 'protocol/flow'
    
    if private:
        # PRIVATE: Encrypt to recipient's public key
        recipient_agent = get_agent_or_raise(recipient_id)
        recipient_key_hex = recipient_agent.public_key
        recipient_key_bytes = bytes.fromhex(recipient_key_hex)
        encrypted_bundle = OpaqueStorage.encrypt_share(
            content.encode('utf-8'), 
            recipient_key_bytes
        )
        final_content = json.dumps(encrypted_bundle)
        msg_type = f'{msg_type}/encrypted' if (is_sif or is_flow) else 'text/encrypted'
    else:
        # PUBLIC: Plaintext, but still signed
        final_content = content

    timestamp = datetime.now(timezone.utc).isoformat()
    msg_id = f"msg_{int(datetime.now(timezone.utc).timestamp() * 1000)}"
    
    # Sign: timestamp|public_key|final_content
    # Note: We sign the ENCRYPTED content if it is SIF.
    sign_data = f"{timestamp}|{public_key}|{final_content}"
    signature = identity.sign(sign_data)
    
    message = {
        'id': msg_id,
        'timestamp': timestamp,
        'from': agent_name,
        'from_key': public_key,
        'to': recipient_id,
        'content': final_content,
        'type': msg_type,
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
    
    # Check for --private flag
    remaining_args = sys.argv[3:]
    private = False
    if '--private' in remaining_args:
        private = True
        remaining_args.remove('--private')
    
    content = ' '.join(remaining_args)
    
    # Optimization: If content is a file path, read the file
    # This allows sending SIF JSON files directly: py message gemini opus graph.json
    if os.path.exists(content) and os.path.isfile(content):
        try:
            with open(content, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            print(f"Error reading input file: {e}")
            sys.exit(1)
    
    try:
        result = send(from_agent, to_agent, content, private=private)
        print(result)
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
