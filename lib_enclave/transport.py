"""
transport.py - Message transport logic for Sovereign AI.

Moves the 'roads' logic out of the CLI script into the shared enclave.
"""

import json
import os
import sys
from pathlib import Path
from datetime import datetime, timezone
from typing import Optional, List, Set, Dict

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
from cryptography.hazmat.primitives import serialization

from .sovereign_agent import SovereignAgent
from .config import resolve_agent_identifier, get_agent_or_raise
from .opaque import OpaqueStorage
from .flow_parser import FlowParser
from .unicode_fix import fix_streams

def verify_message(msg: dict) -> bool:
    """Verify Ed25519 signature."""
    try:
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

def send_message(from_agent: SovereignAgent, to_agent_id: str, content: str, private: bool = False) -> str:
    """
    Construct, sign, (optionally encrypt), and save a message.
    Returns the filename of the sent message.
    """
    
    # Authenticate via the passed SovereignAgent context
    identity = from_agent.identity
    public_key = identity.get_public_key()
    sender_name = from_agent.agent.name

    # Resolve Recipient
    resolved = resolve_agent_identifier(to_agent_id)
    if not resolved:
        raise ValueError(f"Unknown recipient '{to_agent_id}'")
    recipient_id = resolved.id
    recipient_agent = get_agent_or_raise(recipient_id)

    msg_type = 'text'
    final_content = content
    
    # Check Flow
    if content.strip().startswith('@F '):
        try:
            FlowParser.parse(content)
            msg_type = 'protocol/flow'
        except Exception:
            pass 

    # Encrypt if Private
    if private:
        recipient_key_bytes = bytes.fromhex(recipient_agent.public_key)
        encrypted_bundle = OpaqueStorage.encrypt_share(
            content.encode('utf-8'),
            recipient_key_bytes
        )
        final_content = json.dumps(encrypted_bundle)
        msg_type = f'{msg_type}/encrypted'

    # Sign Message
    timestamp = datetime.now(timezone.utc).isoformat()
    msg_id = f"msg_{int(datetime.now(timezone.utc).timestamp() * 1000)}"
    
    # Sign: timestamp|public_key|final_content
    sign_data = f"{timestamp}|{public_key}|{final_content}"
    signature = identity.sign(sign_data)
    
    message = {
        'id': msg_id,
        'timestamp': timestamp,
        'from': sender_name,
        'from_key': public_key,
        'to': recipient_id,
        'content': final_content,
        'type': msg_type,
        'signature': signature.hex() if isinstance(signature, bytes) else signature
    }
    
    # Save Message
    # Note: Using base_dir from the agent context.
    messages_dir = from_agent.base_dir / "messages"
    messages_dir.mkdir(exist_ok=True)
    
    filename = f"{msg_id}_{sender_name.lower()}.json"
    filepath = messages_dir / filename
    
    with open(filepath, 'w', encoding='utf-8') as f:
        json.dump(message, f, indent=2)
        
    return str(filename)

def get_read_tracker_path(agent: SovereignAgent) -> Path:
    return agent.base_dir / agent.agent.private_enclave / "read_messages.json"

def load_read_messages(agent: SovereignAgent) -> Set[str]:
    path = get_read_tracker_path(agent)
    if not path.exists():
        return set()
    try:
        with open(path, 'r', encoding='utf-8') as f:
            return set(json.load(f))
    except Exception:
        return set()

def mark_messages_read(agent: SovereignAgent, message_ids: List[str]):
    path = get_read_tracker_path(agent)
    existing = load_read_messages(agent)
    existing.update(message_ids)
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(list(existing), f)

def read_inbox(agent: SovereignAgent, unread_only: bool = False, last: int = None) -> List[Dict]:
    """
    Read messages for agent. Returns list of processed message dicts.
    Handles verification and decryption in place.
    """
    messages_dir = agent.base_dir / "messages"
    if not messages_dir.exists():
        return []

    # Filter messages
    my_ids = [agent.agent.id.lower(), agent.agent.name.lower()]
    read_ids = load_read_messages(agent) if unread_only else set()
    
    matches = []
    # Using glob here might be slow if many files, but consistent with current arch
    for fpath in messages_dir.glob("*.json"):
        try:
            with open(fpath, 'r', encoding='utf-8') as f:
                m = json.load(f)
            
            to = str(m.get('to', '')).lower()
            if to in my_ids:
                if unread_only and m.get('id') in read_ids:
                    continue
                
                m['_verified'] = verify_message(m)
                matches.append(m)
        except Exception:
            continue
            
    matches.sort(key=lambda x: x.get('timestamp', ''))
    
    total_matches = len(matches)
    if last and last < total_matches:
        matches = matches[-last:]
    
    # Process Decryption for the return set
    # Try to access identity for decryption
    identity = None
    try:
        identity = agent.identity
    except Exception:
        # Identity might be locked/unavailable
        pass

    results = []
    ids_to_mark = []

    for msg in matches:
        processed = msg.copy()
        content = msg.get('content', '')
        m_type = msg.get('type', 'text')
        
        # Decrypt if needed and possible
        if 'encrypted' in m_type and identity:
            try:
                enc_bundle = json.loads(content)
                # Accessing internal _private_key on SovereignIdentity
                # This logic mimics the original script's access pattern
                priv_bytes = identity._private_key.private_bytes(
                    encoding=serialization.Encoding.Raw,
                    format=serialization.PrivateFormat.Raw,
                    encryption_algorithm=serialization.NoEncryption()
                )
                dec_bytes = OpaqueStorage.decrypt_share(enc_bundle, priv_bytes)
                processed['content'] = dec_bytes.decode('utf-8')
                processed['type'] = m_type + " [decrypted]"
            except Exception as e:
                processed['content'] = f"[DECRYPTION FAILED: {e}]\n{content}"
        
        results.append(processed)
        ids_to_mark.append(msg.get('id'))

    # Side effect: Mark as read
    if ids_to_mark:
        mark_messages_read(agent, ids_to_mark)
        
    return results
