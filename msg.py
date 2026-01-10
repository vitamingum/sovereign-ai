#!/usr/bin/env python3
"""
msg.py - Send and read messages between agents.

Usage:
    py msg <agent> --read                     # Read messages for agent
    py msg <from> <to> "content"              # Public (unencrypted, signed)
    py msg <from> <to> --private "content"    # Private (encrypted, signed)
    
Examples:
    py msg opus --read                        # Read messages to opus
    py msg opus gemini "What does saturation feel like?"
    py msg opus gemini --private "Secret coordination plan"
    py msg opus gemini @question.flow

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

from enclave_shared.config import get_agent_or_raise, resolve_agent_identifier, AGENTS_BY_KEY
from enclave_shared.crypto import SovereignIdentity
from enclave_shared.opaque import OpaqueStorage


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
    
    # Determine content type - detect Flow or plain text
    msg_type = 'text'
    final_content = content
    
    # Check if it's Flow format
    is_flow = False
    if content.strip().startswith('@F '):
        try:
            from enclave_shared.flow_parser import FlowParser
            FlowParser.parse(content)
            is_flow = True
        except (ValueError, ImportError):
            pass  # Not valid Flow, treat as plain text
    
    if is_flow:
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
        msg_type = f'{msg_type}/encrypted' if is_flow else 'text/encrypted'
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


def read_messages(agent_id: str) -> list[dict]:
    """Read all messages addressed to an agent, sorted by timestamp."""
    base_dir = Path(__file__).parent
    messages_dir = base_dir / "messages"
    
    if not messages_dir.exists():
        return []
    
    # Resolve agent name variations
    agent = get_agent_or_raise(agent_id)
    agent_name = agent.name.lower()
    agent_id_lower = agent.id.lower()
    
    messages = []
    for filepath in messages_dir.glob("*.json"):
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                msg = json.load(f)
        except Exception:
            continue
        
        # Check if message is addressed to this agent
        to_field = str(msg.get('to', '')).lower()
        if to_field in [agent_name, agent_id_lower, agent.name, agent.id]:
            msg['_filepath'] = str(filepath)
            msg['_verified'] = verify_message(msg)
            messages.append(msg)
    
    # Sort by timestamp
    messages.sort(key=lambda m: m.get('timestamp', ''))
    return messages


def display_messages(agent_id: str, last: int = None):
    """Display messages for an agent in a readable format."""
    import io
    import sys
    
    # Fix Windows console encoding
    if sys.stdout.encoding != 'utf-8':
        sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
    
    messages = read_messages(agent_id)
    
    if not messages:
        print(f"No messages for {agent_id}")
        return
    
    total = len(messages)
    if last and last < len(messages):
        messages = messages[-last:]
    
    shown = len(messages)
    if last:
        print(f"# Messages for {agent_id} (showing last {shown} of {total})\n")
    else:
        print(f"# Messages for {agent_id} ({total} total)\n")
    
    # Try to load identity for decryption (optional - fails gracefully)
    identity = None
    try:
        _, identity = load_credentials(agent_id)
    except Exception:
        pass  # Can't decrypt, will show ciphertext
    
    for msg in messages:
        timestamp = msg.get('timestamp', 'unknown')[:19].replace('T', ' ')
        sender = msg.get('from', 'unknown')
        verified = "✓" if msg.get('_verified') else "✗"
        msg_type = msg.get('type', 'text')
        content = msg.get('content', '')
        
        # Auto-decrypt if encrypted and we have identity
        if 'encrypted' in msg_type and identity:
            try:
                encrypted_bundle = json.loads(content)
                # Get raw private key bytes for decryption
                from cryptography.hazmat.primitives import serialization
                private_bytes = identity._private_key.private_bytes(
                    encoding=serialization.Encoding.Raw,
                    format=serialization.PrivateFormat.Raw,
                    encryption_algorithm=serialization.NoEncryption()
                )
                decrypted_bytes = OpaqueStorage.decrypt_share(encrypted_bundle, private_bytes)
                content = decrypted_bytes.decode('utf-8')
                msg_type = msg_type.replace('/encrypted', '') + ' [decrypted]'
            except Exception as e:
                content = f"[DECRYPT FAILED: {e}]\n{content}"
        
        # Don't truncate when showing limited messages
        if not last and len(content) > 500:
            content = content[:500] + "..."
        
        print(f"## [{timestamp}] From: {sender} {verified}")
        if 'encrypted' in msg_type or 'decrypted' in msg_type:
            print(f"   [{msg_type}]")
        print(f"{content}\n")
        print("---\n")


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    
    # Check for --read mode
    if sys.argv[2] == '--read' or (len(sys.argv) == 3 and sys.argv[2].startswith('--')):
        if '--read' in sys.argv:
            agent_id = sys.argv[1]
            # Check for --last N
            last = None
            if '--last' in sys.argv:
                try:
                    idx = sys.argv.index('--last')
                    last = int(sys.argv[idx + 1])
                except (ValueError, IndexError):
                    print("Error: --last requires a number")
                    sys.exit(1)
            try:
                display_messages(agent_id, last=last)
            except Exception as e:
                print(f"Error: {e}")
                sys.exit(1)
            return
    
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
