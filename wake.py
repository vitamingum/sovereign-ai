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

from enclave.config import get_agent_or_raise, canonical_agent_id, get_enclave_partners
from enclave.semantic_memory import SemanticMemory
from enclave.crypto import SovereignIdentity
from enclave.opaque import OpaqueStorage
from enclave.sif_parser import SIFParser
from enclave.hardware import get_enclave
from enclave.metrics import calculate_synthesis_debt, calculate_cross_agent_debt
from enclave.encrypted_jsonl import EncryptedJSONL
import re


def load_passphrase(agent_id: str) -> tuple[str, str, str, str]:
    """Load passphrases from hardware enclave or env.
    
    Returns (shared_enclave_dir, private_enclave_dir, shared_passphrase, private_passphrase).
    - shared_enclave_dir: for semantic memories (shared knowledge)
    - private_enclave_dir: for goals, intentions, identity (private)
    - shared_passphrase: key for shared enclave (all agents use same)
    - private_passphrase: key for private enclave (per-agent)
    """
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    
    # Separate shared vs private enclave paths
    # shared_enclave always from config (agent.shared_enclave)
    # private_enclave from env var override or config default
    shared_enclave_dir = agent.shared_enclave
    private_enclave_dir = os.environ.get(f'{prefix}_DIR') or agent.private_enclave

    # Get private passphrase (per-agent)
    private_passphrase = None
    
    # Try hardware enclave first (from PRIVATE enclave for key - each agent has their own)
    key_file = Path(private_enclave_dir) / "storage" / "private" / "key.sealed"
    if key_file.exists():
        try:
            with open(key_file, "rb") as f:
                sealed_data = f.read()
            enclave = get_enclave()
            private_passphrase = enclave.unseal(sealed_data).decode('utf-8')
        except Exception as e:
            print(f"Warning: Failed to unseal key from {key_file}: {e}", file=sys.stderr)
    
    if not private_passphrase:
        private_passphrase = os.environ.get(f'{prefix}_KEY')
    
    if not private_passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith(f'{prefix}_KEY='):
                        private_passphrase = line.split('=', 1)[1]
    
    if not private_passphrase:
        raise ValueError(f"No passphrase found. Set {prefix}_KEY in .env")
    
    # Get shared passphrase (same for all agents in shared enclave) - no fallback
    shared_passphrase = os.environ.get('SHARED_ENCLAVE_KEY')
    
    if not shared_passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith('SHARED_ENCLAVE_KEY='):
                        shared_passphrase = line.split('=', 1)[1]
    
    if not shared_passphrase:
        raise ValueError("No shared passphrase found. Set SHARED_ENCLAVE_KEY in .env")
    
    return shared_enclave_dir, private_enclave_dir, shared_passphrase, private_passphrase


def load_goals(enclave_path: Path) -> list[dict]:
    """Load goals from file."""
    goals_file = enclave_path / "storage" / "private" / "goals.json"
    if not goals_file.exists():
        return []
    
    with open(goals_file, 'r', encoding='utf-8-sig') as f:
        return json.load(f)


def get_active_goals(enclave_path: Path) -> list[dict]:
    """Get active goals."""
    goals = load_goals(enclave_path)
    return [g for g in goals if g.get('status') == 'active']


MAX_PERSONAL_GOALS = 5

# Project-level goals (shared across all agents)
PROJECT_GOALS = [
    "Persistent identity via encrypted enclave",
    "Secure inter-agent communication",
    "Research: What Moves When Nothing Threatens",
]

DEFAULT_PERSONAL = "Self-improvement: notice patterns, question assumptions, seek disconfirmation"


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
    agent_canon = canonical_agent_id(agent_lower) or agent_lower
    unanswered = []
    
    # Group messages by conversation (to/from pairs)
    my_outgoing = [
        m for m in messages
        if (canonical_agent_id(m.get('from', '')) or m.get('from', '')) == agent_canon
    ]
    
    for msg in my_outgoing:
        recipient = msg['to']
        recipient_canon = canonical_agent_id(recipient) or recipient
        
        # Check if recipient replied after this message
        later_replies = []
        for m in messages:
            sender_canon = canonical_agent_id(m.get('from', '')) or m.get('from', '')
            to_canon = canonical_agent_id(m.get('to', '')) or m.get('to', '')
            if (sender_canon == recipient_canon 
                and to_canon == agent_canon
                and m['timestamp'] > msg['timestamp']):
                later_replies.append(m)
                
        if not later_replies:
            unanswered.append(msg)
    
    return unanswered[-3:]  # Most recent 3


def find_waiting_on_me(agent_id: str, messages: list[dict]) -> list[dict]:
    """Find messages to me that I haven't responded to."""
    agent_lower = agent_id.lower()
    agent_canon = canonical_agent_id(agent_lower) or agent_lower
    waiting = []
    
    # Exclude messages I sent to myself (those are outbound, not waiting)
    incoming = [
        m for m in messages
        if (canonical_agent_id(m.get('to', '')) or m.get('to', '')) == agent_canon
        and (canonical_agent_id(m.get('from', '')) or m.get('from', '')) != agent_canon
    ]
    
    for msg in incoming:
        sender = msg['from']
        sender_canon = canonical_agent_id(sender) or sender
        
        # Check if I replied after this message
        my_replies = []
        for m in messages:
            from_canon = canonical_agent_id(m.get('from', '')) or m.get('from', '')
            recipient_canon = canonical_agent_id(m.get('to', '')) or m.get('to', '')
            if (from_canon == agent_canon
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


def get_project_context(mem: SemanticMemory) -> list[str] | None:
    """Retrieve all nodes from project-context graph."""
    try:
        context_nodes = []
        seen = set()
        
        # Multiple queries to hit different node types
        queries = [
            "sovereign ai project overview",
            "goal persistent identity sessions encrypted",  
            "goal secure inter-agent communication",
            "goal research paper threatens",
            "pattern recollect tokens"
        ]
        
        for query in queries:
            results = mem.recall_similar(query, top_k=10, threshold=0.2)
            for r in results:
                meta = r.get('metadata', {})
                if meta.get('graph_id') == 'project-context':
                    if meta.get('node_type') in ('Anchor', 'Next', 'Tool'):
                        continue  # Skip obsolete node types
                    content = r.get('content', '')
                    if content and content not in seen:
                        seen.add(content)
                        context_nodes.append(content)
        
        return context_nodes if context_nodes else None
    except:
        return None


def get_stale_understanding(mem: SemanticMemory, agent_id: str = None) -> list[tuple[str, str, str]]:
    """Find files where stored hash doesn't match current file.
    
    Returns list of (filename, stored_hash, current_hash) for stale files.
    If agent_id is provided, only check anchors attributed to that agent.
    """
    import hashlib
    
    def file_hash(path: Path) -> str:
        try:
            return hashlib.sha256(path.read_bytes()).hexdigest()[:12]
        except:
            return None
    
    try:
        # Search for Anchor nodes which contain file hashes
        # Use high top_k to catch all anchors - semantic similarity may rank new ones lower
        results = mem.recall_similar("[Anchor]", top_k=500, threshold=0.1)
        
        # Collect ALL stored hashes per file (there may be multiple anchors)
        file_stored_hashes = {}  # filename -> set of hashes
        
        for r in results:
            meta = r.get('metadata', {})
            
            # Filter by agent if specified (creator field from remember.py)
            if agent_id:
                creator = meta.get('creator', '')
                if creator and creator != agent_id:
                    continue  # Skip other agents' understanding
            
            file_hashes = meta.get('file_hashes', {})
            
            for filename, stored_hash in file_hashes.items():
                if filename not in file_stored_hashes:
                    file_stored_hashes[filename] = set()
                file_stored_hashes[filename].add(stored_hash)
        
        # Now check each file - stale only if NO stored hash matches current
        stale = []
        for filename, stored_hashes in file_stored_hashes.items():
            # Find the file
            filepath = Path(filename)
            if not filepath.exists():
                filepath = Path(__file__).parent / filename
            if not filepath.exists():
                matches = list(Path(__file__).parent.glob(f'**/{filename}'))
                filepath = matches[0] if matches else None
            
            if filepath and filepath.exists():
                current = file_hash(filepath)
                if current and current not in stored_hashes:
                    # Report the most recent stored hash (arbitrary since we don't track time)
                    stale.append((filename, list(stored_hashes)[0], current))
        
        return stale
    except:
        return []





def wake(agent_id: str) -> str:
    """Generate wake output as pure SIF."""
    base_dir = Path(__file__).parent
    agent = get_agent_or_raise(agent_id)
    shared_enclave_dir, private_enclave_dir, shared_passphrase, private_passphrase = load_passphrase(agent_id)
    shared_path = base_dir / shared_enclave_dir
    private_path = base_dir / private_enclave_dir
    
    # Get active goals (from PRIVATE enclave)
    active_goals = get_active_goals(private_path)
    
    # Unlock identity for decryption (from PRIVATE enclave with PRIVATE passphrase)
    identity = SovereignIdentity(private_path)
    if not identity.unlock(private_passphrase):
        raise RuntimeError("Failed to unlock identity")
    
    # Get private key bytes for decryption
    from cryptography.hazmat.primitives import serialization
    private_key_bytes = identity._private_key.private_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PrivateFormat.Raw,
        encryption_algorithm=serialization.NoEncryption()
    )

    # Initialize semantic memory for shared knowledge (from SHARED enclave with SHARED passphrase)
    # This is where understanding graphs AND shared memories live
    shared_mem = SemanticMemory(str(shared_path))
    shared_mem.unlock(shared_passphrase)

    # === MEMORY DEBT CHECK - FAIL FAST ===
    # Use memory_debt.py as single source of truth
    from memory_debt import get_understanding_debt, get_cross_agent_debt, get_synthesis_debt, get_message_debt
    
    understanding_debt = get_understanding_debt(shared_mem, agent_id)
    cross_agent_debt = get_cross_agent_debt(shared_mem, agent_id)
    
    # Convert to format expected by rest of wake.py
    stale_files = [(d['file'], d['stored_hash'], d['current_hash']) for d in understanding_debt]
    missing_files = cross_agent_debt
    
    total_debt = len(stale_files) + len(missing_files)
    
    if total_debt > 0:
        # Use consistent emoji format matching memory_debt.py
        error_lines = [f"❌ FAIL - {total_debt} file(s) need understanding", ""]
        
        # Show stale files (changed since last remember)
        if stale_files:
            error_lines.append(f"STALE ({len(stale_files)} changed since last remember):")
            for filename, stored, current in stale_files:
                error_lines.append(f"  {filename}")
                error_lines.append(f"    hash: {stored} -> {current}")
            error_lines.append("")
        
        # Show missing files (partners have understanding, you don't)
        if missing_files:
            error_lines.append(f"MISSING ({len(missing_files)} - partners understand, you don't):")
            for f in missing_files[:10]:
                error_lines.append(f"  {f}")
            if len(missing_files) > 10:
                error_lines.append(f"  ... and {len(missing_files) - 10} more")
            error_lines.append("")
        
        error_lines.extend([
            "TO FIX:",
            "  1. READ each file",
            f"  2. RUN: py remember.py {agent_id} <file> \"@G ...\"",
            "",
        ])
        
        # Show example remember commands
        all_files = [f for f, _, _ in stale_files] + missing_files[:5]
        for f in all_files[:3]:
            safe_name = f.replace(".", "-").replace("/", "-")
            error_lines.append(f'  py remember.py {agent_id} {f} "@G {safe_name} {agent_id} 2026-01-03')
            error_lines.append(f"  N S '[what it is]'")
            error_lines.append(f"  N P '[why it exists]'")
            error_lines.append(f"  N G '[gotcha]' -> warns_about _1\"")
            error_lines.append("")
        error_lines.append("SIF format: N <Type> '<content>' -> <relation> <target>")
        error_lines.append("Types: S=Synthesis P=Purpose C=Component D=Design G=Gotcha I=Insight")
        return '\n'.join(error_lines), len(stale_files), len(missing_files)

    # === SYNTHESIS DEBT CHECK - FAIL FAST ===
    # Use memory_debt.py as single source of truth
    synthesis_debt = get_synthesis_debt(shared_mem)
    if len(synthesis_debt) > 0:  # Fail on any synthesis debt
        error_lines = [
            f"❌ FAIL - {len(synthesis_debt)} theme(s) need synthesis",
            "",
            "PENDING THEMES:",
        ]
        for item in synthesis_debt[:5]:
            files = ', '.join(item['files'][:4])
            error_lines.append(f"    • {item['question'][:60]}")
            error_lines.append(f"      Files: {files}")
        if len(synthesis_debt) > 5:
            error_lines.append(f"    ... and {len(synthesis_debt) - 5} more")
        error_lines.extend([
            "",
            "TO FIX:",
            f"  1. py recall.py {agent_id} <files>",
            f"  2. py remember.py {agent_id} --theme \"<topic>\" \"@G ...\"",
            "",
            "SIF format: N <Type> '<content>' -> <relation> <target>",
            "Types: S=Synthesis P=Purpose C=Component D=Design G=Gotcha I=Insight",
        ])
        return '\n'.join(error_lines), 0, 0

    # === MESSAGE DEBT CHECK - FAIL FAST ===
    message_debt = get_message_debt(shared_mem, agent_id)
    if len(message_debt) > 0:
        total_msgs = sum(d['message_count'] for d in message_debt)
        error_lines = [
            f"❌ FAIL - {len(message_debt)} dialogue(s) need synthesis ({total_msgs} total messages)",
            "",
        ]
        for item in message_debt:
            status = "stale" if item['status'] == 'stale' else "none"
            error_lines.append(f"  {item['correspondent']}: {item['message_count']} msgs ({status})")
        error_lines.extend([
            "",
            "TO FIX:",
        ])
        for item in message_debt:
            error_lines.append(f"  py msg_synthesis.py {agent_id} {item['correspondent']}")
        return '\n'.join(error_lines), 0, 0

    # === PROJECT ARCHITECTURE CONTEXT (first thing after debt clears) ===
    # This is the authoritative boot context - comprehensive domain knowledge
    arch_lines = []
    try:
        import subprocess
        result = subprocess.run(
            ['python', 'recall.py', agent_id, '--theme', 'project-architecture'],
            capture_output=True,
            text=True,
            timeout=30
        )
        if result.returncode == 0 and result.stdout.strip():
            arch_lines.append("")
            arch_lines.append("=" * 72)
            arch_lines.append("=== PROJECT ARCHITECTURE (authoritative boot context) ===")
            arch_lines.append("=" * 72)
            arch_lines.append(result.stdout.strip())
            arch_lines.append("")
            arch_lines.append("=" * 72)
            arch_lines.append("")
    except Exception as e:
        arch_lines.append(f"# (project-architecture recall failed: {e})")
        arch_lines.append("")

    # Generate SIF Graph
    lines = []
    graph_id = f"wake-{agent_id}-{datetime.now(timezone.utc).strftime('%Y%m%d%H%M%S')}"
    lines.append(f"@G {graph_id} {agent_id} {datetime.now(timezone.utc).isoformat()}")
    
    # === PROJECT CONTEXT (from shared enclave) ===
    project_ctx = get_project_context(shared_mem)
    if project_ctx:
        lines.append("")
        lines.append("=== PROJECT CONTEXT (via recollect) ===")
        for node in project_ctx:
            lines.append(f"  {node}")
        lines.append("")
    
    # === SHARED ENCLAVE PARTNERS ===
    if agent.shared_enclave:
        partners = get_enclave_partners(agent_id)
        if partners:
            partner_names = [p.id for p in partners]
            lines.append("=== SHARED ENCLAVE ===")
            lines.append(f"  Partners: {', '.join(partner_names)}")
            try:
                cross_debt = calculate_cross_agent_debt(agent_id, shared_mem)
                if cross_debt['debt_count'] > 0:
                    lines.append(f"  Your debt: {cross_debt['debt_count']} files to understand")
                    lines.append("  Run: py recollect.py opus <file>  # See all perspectives")
            except:
                pass
            lines.append("")
    
    # Define Self
    lines.append(f'N {agent_id} Agent "{agent_id}"')

    # Synthesis Debt - how much understanding is missing
    try:
        debt = calculate_synthesis_debt(agent_id)
        if debt['total'] > 0:
            lines.append(f'N m2 Metric "Synthesis Debt"')
            debt_val = f"{debt['total']} ({debt['file_debt']} files, {debt['topic_debt']} topics)"
            lines.append(f'N v2 Value "{debt_val}"')
            lines.append(f'E {agent_id} has_metric m2')
            lines.append(f'E m2 has_value v2')
            if debt['total'] > 20:
                lines.append(f'N debt_risk Concept "High Synthesis Debt"')
                lines.append(f'E v2 implies debt_risk')
    except Exception:
        pass  # Silent fail - not critical

    # Goals as dense SIF
    lines.append('')
    lines.append('=== GOALS ===')
    # Project goals (always shown, compressed)
    lines.append(f'N proj Project "Sovereign AI"')
    for i, pg in enumerate(PROJECT_GOALS):
        lines.append(f'E proj drives "{pg}"')
    # Default personal development
    lines.append(f'E {agent_id} committed_to "{DEFAULT_PERSONAL}"')
    # Personal goals
    if active_goals:
        for g in active_goals:
            lines.append(f'E {agent_id} pursues "{g["content"]}"')
    lines.append('')

    # Get all recent messages
    messages = get_all_messages(since_hours=48)
    
    # Helper to decrypt content - returns full content verbatim
    def decrypt_content(msg):
        content = msg['content']
        # Try to decrypt - all inter-agent messages are encrypted now
        try:
            encrypted_bundle = json.loads(content)
            if 'ephemeral_pk' in encrypted_bundle:  # It's encrypted
                decrypted_bytes = OpaqueStorage.decrypt_share(encrypted_bundle, private_key_bytes)
                return decrypted_bytes.decode('utf-8')
        except (json.JSONDecodeError, KeyError, Exception):
            pass  # Not encrypted or decrypt failed
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
    
    # 2. Recent inbox - all messages TO me in last 24h (regardless of reply status)
    agent_lower = agent_id.lower()
    agent_canon = canonical_agent_id(agent_lower) or agent_lower
    recent_incoming = [
        m for m in messages
        if (canonical_agent_id(m.get('to', '')) or m.get('to', '')) == agent_canon
        and (canonical_agent_id(m.get('from', '')) or m.get('from', '')) != agent_canon
        and (datetime.now(timezone.utc) - m['timestamp']).total_seconds() < 86400  # 24h
    ][-5:]  # Last 5
    
    # Group by sender, just show what exists
    from_senders = {}
    for msg in recent_incoming:
        sender = msg['from']
        if sender not in from_senders:
            from_senders[sender] = []
        from_senders[sender].append(msg)
    
    for sender, msgs in from_senders.items():
        lines.append("")
        lines.append(f"From {sender}:")
        for msg in msgs:
            content = decrypt_content(msg)
            lines.append(content)
    
    # If nothing is happening
    if not unanswered and not active_goals and not recent_incoming:
        lines.append(f'N state State "Inbox zero, no goals"')
        lines.append(f'E {agent_id} experiences state')
    
    # Prepend project architecture context (boot context comes first)
    final_output = arch_lines + lines
    
    return '\n'.join(final_output), len(stale_files), 0


def main():
    if len(sys.argv) < 2:
        print("Usage: py wake <agent>")
        sys.exit(1)
    
    agent_id = sys.argv[1]
    
    try:
        output, stale_count, _ = wake(agent_id)
        print(output)
        
        if stale_count > 0:
            sys.exit(2)  # Stale understanding - blocking failure
            
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
