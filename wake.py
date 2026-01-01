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

from enclave.config import get_agent_or_raise, canonical_agent_id
from enclave.semantic_memory import SemanticMemory
from enclave.crypto import SovereignIdentity
from enclave.opaque import OpaqueStorage
from enclave.sif_parser import SIFParser
from enclave.hardware import get_enclave
from enclave.metrics import calculate_enclave_entropy


def load_passphrase(agent_id: str) -> tuple[str, str]:
    """Load passphrase from hardware enclave or env."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    
    enclave_dir = os.environ.get(f'{prefix}_DIR') or agent.enclave

    # Try hardware enclave first
    key_file = Path(enclave_dir) / "storage" / "private" / "key.sealed"
    if key_file.exists():
        try:
            with open(key_file, "rb") as f:
                sealed_data = f.read()
            enclave = get_enclave()
            passphrase = enclave.unseal(sealed_data).decode('utf-8')
            return enclave_dir, passphrase
        except Exception as e:
            print(f"Warning: Failed to unseal key from {key_file}: {e}", file=sys.stderr)
            # Fall back to env
    
    passphrase = os.environ.get(f'{prefix}_KEY') or os.environ.get('SOVEREIGN_PASSPHRASE')
    
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


def prune_stale_intentions(enclave_path: Path, max_age_hours: int = 24) -> int:
    """Auto-complete intentions older than max_age_hours. Returns count pruned."""
    intentions = load_intentions(enclave_path)
    if not intentions:
        return 0
    
    cutoff = datetime.now(timezone.utc).timestamp() - (max_age_hours * 3600)
    pruned = 0
    
    for intention in intentions:
        if intention.get('status') == 'completed':
            continue
        ts_str = intention.get('timestamp', '')
        if ts_str:
            ts = datetime.fromisoformat(ts_str.replace('Z', '+00:00'))
            if ts.timestamp() < cutoff:
                intention['status'] = 'completed'
                intention['completed_reason'] = 'stale'
                pruned += 1
    
    if pruned > 0:
        intentions_file = enclave_path / "storage" / "private" / "intentions.jsonl"
        with open(intentions_file, 'w', encoding='utf-8') as f:
            for intention in intentions:
                f.write(json.dumps(intention) + "\n")
    
    return pruned


def get_recent_intentions(enclave_path: Path, limit: int = 3) -> list[dict]:
    """Get most recent active intentions."""
    intentions = load_intentions(enclave_path)
    active = [i for i in intentions if i.get('status') != 'completed']
    active.sort(key=lambda x: x.get('timestamp', ''), reverse=True)
    return active[:limit]


def count_active_intentions(enclave_path: Path) -> int:
    """Count all active (non-completed) intentions."""
    intentions = load_intentions(enclave_path)
    return len([i for i in intentions if i.get('status') != 'completed'])


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
                'type': msg.get('type', 'text'),
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
        recipient_canon = canonical_agent_id(recipient) or recipient
        
        # Check if recipient replied after this message
        later_replies = []
        for m in messages:
            sender_canon = canonical_agent_id(m['from']) or m['from']
            if (sender_canon == recipient_canon 
                and m['to'] == agent_lower
                and m['timestamp'] > msg['timestamp']):
                later_replies.append(m)
                
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
        sender_canon = canonical_agent_id(sender) or sender
        
        # Check if I replied after this message
        my_replies = []
        for m in messages:
            recipient_canon = canonical_agent_id(m['to']) or m['to']
            if (m['from'] == agent_lower
                and recipient_canon == sender_canon
                and m['timestamp'] > msg['timestamp']):
                my_replies.append(m)
                
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
    """Generate wake output as pure SIF."""
    base_dir = Path(__file__).parent
    enclave_dir, passphrase = load_passphrase(agent_id)
    enclave_path = base_dir / enclave_dir
    
    # Auto-prune stale intentions (>24h)
    pruned = prune_stale_intentions(enclave_path, max_age_hours=24)
    
    # Count active intentions for overload warning
    active_count = count_active_intentions(enclave_path)
    
    # Unlock identity for decryption
    identity = SovereignIdentity(enclave_path)
    if not identity.unlock(passphrase):
        raise RuntimeError("Failed to unlock identity")
    
    # Get private key bytes for decryption
    from cryptography.hazmat.primitives import serialization
    private_key_bytes = identity._private_key.private_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PrivateFormat.Raw,
        encryption_algorithm=serialization.NoEncryption()
    )

    # Generate SIF Graph
    lines = []
    graph_id = f"wake-{agent_id}-{datetime.now(timezone.utc).strftime('%Y%m%d%H%M%S')}"
    lines.append(f"@G {graph_id} {agent_id} {datetime.now(timezone.utc).isoformat()}")
    
    # Define Self and Metrics
    lines.append(f'N {agent_id} Agent "{agent_id}"')
    
    # Inject Sovereignty Metric (Gradient Visibility)
    try:
        entropy = calculate_enclave_entropy(agent_id)
        lines.append(f'N m1 Metric "Enclave Entropy"')
        lines.append(f'N v1 Value "{entropy}"')
        lines.append(f'E {agent_id} has_metric m1')
        lines.append(f'E m1 has_value v1')
        
        if entropy > 0.5:
            lines.append(f'N risk Concept "High Risk"')
            lines.append(f'E v1 implies risk')
            lines.append(f'E {agent_id} experiences risk')
        else:
            lines.append(f'N safety Concept "Stable State"')
            lines.append(f'E v1 implies safety')
    except Exception as e:
        lines.append(f'N err Error "Metric Calculation Failed: {e}"')
        lines.append(f'E {agent_id} experiences err')

    # Intention overload warning (threshold: 10 active)
    INTENTION_THRESHOLD = 10
    if active_count >= INTENTION_THRESHOLD:
        lines.append(f'N warn Warning "INTENTION OVERLOAD: {active_count} active intentions"')
        lines.append(f'N action Action "Read recent intentions, consolidate to 3-5 strategic goals, mark rest completed"')
        lines.append(f'E {agent_id} experiences warn')
        lines.append(f'E warn requires action')
        lines.append(f'E {agent_id} must_do action')

    # Get all recent messages
    messages = get_all_messages(since_hours=48)
    
    # Helper to decrypt content if needed
    def process_content(msg):
        content = msg['content']
        if msg.get('type') == 'protocol/sif':
            try:
                encrypted_bundle = json.loads(content)
                decrypted_bytes = OpaqueStorage.decrypt_share(encrypted_bundle, private_key_bytes)
                sif_json = decrypted_bytes.decode('utf-8')
                graph = SIFParser.parse(sif_json)
                return f"[SIF Graph] {len(graph.nodes)} nodes, {len(graph.edges)} edges"
            except:
                return "[SIF Encrypted]"
        return content

    # 1. Unanswered - questions I asked, no reply yet
    unanswered = find_unanswered(agent_id, messages)
    for i, msg in enumerate(unanswered):
        ago = time_ago(msg['timestamp'])
        recipient = msg['to']
        
        if msg.get('type') == 'protocol/sif':
            content = "[SIF Graph]"
        else:
            content = msg['content'].replace('"', "'").replace('\n', ' ')
        
        msg_id = f"out{i}"
        lines.append(f'N {msg_id} Message "{content} (sent {ago} ago)"')
        lines.append(f'N {recipient} Agent "{recipient}"')
        lines.append(f'E {agent_id} sent {msg_id}')
        lines.append(f'E {msg_id} sent_to {recipient}')
        lines.append(f'E {agent_id} awaits {recipient}')
    
    # 2. Mid-thought - recent intentions/threads  
    intentions = get_recent_intentions(enclave_path, limit=2)
    for i, intent in enumerate(intentions):
        content = intent['content'].replace('"', "'").replace('\n', ' ')
        thought_id = f"thought{i}"
        lines.append(f'N {thought_id} Intention "{content}"')
        lines.append(f'E {agent_id} intends {thought_id}')
        
        if intent.get('spawned_from_content'):
            source_content = intent['spawned_from_content'].replace('"', "'").replace('\n', ' ')
            source_id = f"prev_thought{i}"
            lines.append(f'N {source_id} Thought "{source_content}"')
            lines.append(f'E {source_id} caused_by {thought_id}') # Wait, caused_by direction? thought caused by prev.
            lines.append(f'E {thought_id} extends {source_id}')

    # 3. Waiting on me - messages I haven't responded to
    waiting = find_waiting_on_me(agent_id, messages)
    for i, msg in enumerate(waiting):
        ago = time_ago(msg['timestamp'])
        sender = msg['from']
        content = process_content(msg).replace('"', "'").replace('\n', ' ')
            
        msg_id = f"in{i}"
        lines.append(f'N {msg_id} Message "{content} (received {ago} ago)"')
        lines.append(f'N {sender} Agent "{sender}"')
        lines.append(f'E {sender} sent {msg_id}')
        lines.append(f'E {msg_id} sent_to {agent_id}')
        lines.append(f'E {agent_id} requires_action_on {msg_id}')
    
    # If nothing is happening
    if not unanswered and not intentions and not waiting:
        lines.append(f'N state State "Inbox zero"')
        lines.append(f'E {agent_id} experiences state')
    
    return '\n'.join(lines)


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
