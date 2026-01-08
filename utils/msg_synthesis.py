#!/usr/bin/env python3
"""
msg_synthesis.py - Synthesize all messages with an agent (or all agents).

Creates dialogue synthesis - not two monologues, but what we figured out together.

Usage:
    py msg_synthesis.py opus gemini         # Synthesize dialogue with Gemini
    py msg_synthesis.py opus --all          # Synthesize all agent dialogues
    py msg_synthesis.py opus --list         # List agents with unsynced messages

The synthesis is stored as a theme (e.g., --theme gemini) for instant recall.
"""

import sys
import os
import json
from pathlib import Path
from datetime import datetime
from collections import defaultdict

# Add repo root (parent of utils/) to path for enclave imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from dotenv import load_dotenv
load_dotenv()

from enclave.semantic_memory import SemanticMemory
from enclave.sif_parser import SIFParser
from enclave.config import get_agent_or_raise, AGENTS_BY_KEY
from enclave.opaque import OpaqueStorage
from wake import load_passphrase, SovereignIdentity


def get_agent_messages(agent_id: str) -> dict[str, list[dict]]:
    """
    Get all messages involving this agent, grouped by correspondent.
    
    Returns: {correspondent: [messages sorted by time]}
    """
    messages_dir = Path(__file__).parent.parent / "messages"
    agent = get_agent_or_raise(agent_id)
    agent_name = agent.name
    
    # Normalize agent names (handle variations like gpt-5.2 vs gpt52)
    def normalize_name(name: str) -> str:
        name = name.lower()
        # Map variations to canonical names
        if name in ('gpt-5.2', 'gpt52', 'gpt'):
            return 'gpt52'
        return name
    
    # Group messages by the OTHER agent in the conversation
    conversations = defaultdict(list)
    
    for msg_file in messages_dir.glob("msg_*.json"):
        try:
            with open(msg_file, 'r') as f:
                msg = json.load(f)
            
            from_agent = normalize_name(msg.get('from', ''))
            to_agent = normalize_name(msg.get('to', ''))
            my_name = normalize_name(agent_name)
            
            # Is this agent involved?
            if from_agent == my_name:
                # We sent this message
                correspondent = to_agent
                direction = 'sent'
            elif to_agent == normalize_name(agent_id):
                # We received this message
                correspondent = from_agent
                direction = 'received'
            else:
                continue
            
            # Skip self-messages and broadcast
            if correspondent == my_name or correspondent == 'all':
                continue
            
            conversations[correspondent].append({
                'timestamp': msg.get('timestamp'),
                'direction': direction,
                'from': from_agent,
                'to': to_agent,
                'content': msg.get('content'),
                'type': msg.get('type', 'text'),
                'file': msg_file.name
            })
        except Exception as e:
            continue
    
    # Sort each conversation by timestamp
    for correspondent in conversations:
        conversations[correspondent].sort(key=lambda m: m['timestamp'])
    
    return dict(conversations)


def decrypt_message(agent_id: str, msg: dict) -> str | None:
    """Decrypt an encrypted message if we're the recipient."""
    if 'encrypted' not in msg.get('type', ''):
        return msg.get('content')
    
    # Only decrypt if we're the recipient
    if msg['direction'] != 'received':
        # We sent this encrypted - we can't read it (recipient's key)
        return "[encrypted - sent to recipient]"
    
    try:
        agent = get_agent_or_raise(agent_id)
        base_dir = Path(__file__).parent
        enclave_path = base_dir / agent.private_enclave
        
        _, private_dir, _, private_pass = load_passphrase(agent_id)
        identity = SovereignIdentity(base_dir / private_dir)
        identity.unlock(private_pass)
        
        from cryptography.hazmat.primitives import serialization
        private_key_bytes = identity._private_key.private_bytes(
            encoding=serialization.Encoding.Raw,
            format=serialization.PrivateFormat.Raw,
            encryption_algorithm=serialization.NoEncryption()
        )
        
        bundle = json.loads(msg['content'])
        decrypted = OpaqueStorage.decrypt_share(bundle, private_key_bytes)
        return decrypted.decode('utf-8')
    except Exception as e:
        return f"[decrypt failed: {e}]"


def get_existing_synthesis_timestamp(sm: SemanticMemory, correspondent: str) -> str | None:
    """Check if we have an existing synthesis for this correspondent."""
    topic_tag = f"topic:{correspondent}"
    
    try:
        # Use list_by_tag instead of recall_similar - tags are at top level, not in metadata
        results = sm.list_by_tag('synthesis', limit=100)
        for r in results:
            tags = r.get('tags', [])
            if topic_tag in tags:
                # Get timestamp from metadata.stored_at
                meta = r.get('metadata', {})
                return meta.get('stored_at') or meta.get('timestamp') or r.get('timestamp')
    except:
        pass
    return None


def get_last_message_timestamp(messages: list[dict]) -> str:
    """Get the latest timestamp from a list of messages."""
    if not messages:
        return None
    return max(m['timestamp'] for m in messages)


def list_synthesis_gaps(agent_id: str, conversations: dict, sm: SemanticMemory):
    """List agents with unsynthesized or stale message synthesis."""
    gaps = []
    
    for correspondent, messages in conversations.items():
        if not messages:
            continue
        
        last_msg = get_last_message_timestamp(messages)
        existing_synthesis = get_existing_synthesis_timestamp(sm, correspondent)
        
        if existing_synthesis is None:
            gaps.append({
                'correspondent': correspondent,
                'message_count': len(messages),
                'last_message': last_msg,
                'status': 'none',
                'cmd': f'py remember.py {agent_id} --dialogue {correspondent}'
            })
        elif last_msg > existing_synthesis:
            gaps.append({
                'correspondent': correspondent,
                'message_count': len(messages),
                'last_message': last_msg,
                'synthesis': existing_synthesis,
                'status': 'stale',
                'cmd': f'py remember.py {agent_id} --dialogue {correspondent}'
            })
    
    return gaps


def format_message_for_context(msg: dict, decrypted_content: str) -> str:
    """Format a single message for synthesis context."""
    direction = "->" if msg['direction'] == 'sent' else "<-"
    timestamp = msg['timestamp'][:10]  # Just date
    
    # Truncate very long messages
    content = decrypted_content
    if len(content) > 500:
        content = content[:500] + "..."
    
    return f"[{timestamp}] {direction} {msg['from']}: {content}"


def synthesize_dialogue(agent_id: str, correspondent: str, messages: list[dict]) -> str:
    """
    Generate dialogue synthesis prompt for manual SIF creation.
    
    Returns formatted context for the agent to synthesize.
    """
    output = []
    output.append(f"# Dialogue with {correspondent.capitalize()}")
    output.append(f"# {len(messages)} messages")
    output.append("")
    
    for msg in messages:
        decrypted = decrypt_message(agent_id, msg)
        output.append(format_message_for_context(msg, decrypted))
    
    output.append("")
    output.append("---")
    output.append(f"# Synthesize this dialogue as Flow:")
    output.append(f"# py remember.py {agent_id} {correspondent} @synthesis.flow")
    
    return "\n".join(output)


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    
    # Get enclave
    shared_dir, _, shared_pass, _ = load_passphrase(agent_id)
    sm = SemanticMemory(shared_dir)
    sm.unlock(shared_pass)
    
    # Get all conversations
    conversations = get_agent_messages(agent_id)
    
    if len(sys.argv) < 3 or sys.argv[2] == '--list':
        # List synthesis gaps
        gaps = list_synthesis_gaps(agent_id, conversations, sm)
        
        if not gaps:
            print("✅ All message dialogues synthesized")
            return
        
        print(f"MESSAGE SYNTHESIS GAPS: {len(gaps)}")
        for item in gaps:
            status = "⚠️ stale" if item['status'] == 'stale' else "❌ none"
            print(f"\n{item['correspondent']}: {item['message_count']} messages ({status})")
            print(f"  {item['cmd']}")
        
        sys.exit(len(gaps))
    
    elif sys.argv[2] == '--all':
        # Synthesize all
        gaps = list_synthesis_gaps(agent_id, conversations, sm)
        for item in gaps:
            correspondent = item['correspondent']
            messages = conversations[correspondent]
            print(synthesize_dialogue(agent_id, correspondent, messages))
            print("\n" + "="*60 + "\n")
    
    else:
        # Synthesize specific correspondent
        correspondent = sys.argv[2].lower()
        
        if correspondent not in conversations:
            print(f"No messages found with '{correspondent}'")
            print(f"Available: {', '.join(conversations.keys())}")
            sys.exit(1)
        
        messages = conversations[correspondent]
        print(synthesize_dialogue(agent_id, correspondent, messages))


if __name__ == "__main__":
    main()
