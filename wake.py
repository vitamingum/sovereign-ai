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
    
    # Exclude messages I sent to myself (those are outbound, not waiting)
    incoming = [m for m in messages if m['to'] == agent_lower and m['from'] != agent_lower]
    
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


def get_available_understanding(mem: SemanticMemory) -> list[str]:
    """Find all files that have stored understanding (via remember.py)."""
    try:
        # Search for Component nodes which are the primary anchors
        results = mem.recall_similar("[Component]", top_k=100, threshold=0.1)
        
        files = set()
        for r in results:
            meta = r.get('metadata', {})
            target_path = meta.get('target_path', '')
            graph_id = meta.get('graph_id', '')
            
            # Skip project-context (shown separately)
            if graph_id == 'project-context':
                continue
                
            if target_path:
                # Handle comma-separated multi-file paths
                for p in target_path.split(','):
                    p = p.strip()
                    if p:
                        files.add(p)
        
        return sorted(files)
    except:
        return []


def get_stale_understanding(mem: SemanticMemory) -> list[tuple[str, str, str]]:
    """Find files where stored hash doesn't match current file.
    
    Returns list of (filename, stored_hash, current_hash) for stale files.
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


def get_synthesis_opportunities(mem: SemanticMemory, limit: int = 3) -> list[tuple[str, str]]:
    """Find distant concepts that might connect - synthesis fodder.
    
    Returns list of (concept_a, concept_b) pairs from different domains.
    """
    import random
    
    try:
        # Get diverse nodes by querying different concept types
        seen_content = set()  # Deduplicate by content
        all_insights = []
        for query in ["Insight", "Observation", "Question", "Hypothesis"]:
            results = mem.recall_similar(f"[{query}]", top_k=50, threshold=0.1)
            for r in results:
                meta = r.get('metadata', {})
                if meta.get('node_type') in ('Insight', 'Observation', 'Question', 'Hypothesis'):
                    content = r.get('content', '')
                    graph_id = meta.get('graph_id', '')
                    content_key = content[:80]
                    if content and len(content) > 20 and content_key not in seen_content:
                        seen_content.add(content_key)
                        all_insights.append((content_key, graph_id))
        
        if len(all_insights) < 4:
            return []
        
        # Find pairs from DIFFERENT graphs (different contexts)
        # Each insight should only appear once across all pairs
        pairs = []
        used_insights = set()
        random.shuffle(all_insights)
        
        for i, (a, ga) in enumerate(all_insights):
            if a in used_insights:
                continue
            for b, gb in all_insights[i+1:]:
                if b in used_insights:
                    continue
                if ga != gb:  # Different source graphs
                    pairs.append((a, b))
                    used_insights.add(a)
                    used_insights.add(b)
                    break  # Move to next 'a'
            if len(pairs) >= limit:
                break
        
        return pairs[:limit]
    except:
        return []


def wake(agent_id: str) -> str:
    """Generate wake output as pure SIF."""
    base_dir = Path(__file__).parent
    enclave_dir, passphrase = load_passphrase(agent_id)
    enclave_path = base_dir / enclave_dir
    
    # Get active goals
    active_goals = get_active_goals(enclave_path)
    
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

    # Initialize semantic memory for project context
    mem = SemanticMemory(str(enclave_path))
    mem.unlock(passphrase)

    # === STALE CHECK FIRST - FAIL FAST ===
    stale_files = get_stale_understanding(mem)
    if stale_files:
        # Format like a Python traceback to trigger "broken" instinct
        error_lines = [
            "Traceback (most recent call last):",
            f'  File "wake.py", line 1, in <module>',
            "    from sovereign.memory import understanding",
        ]
        for filename, stored, current in stale_files:
            error_lines.append(f'  File "{filename}", line 1')
            error_lines.append(f"    # hash: {stored} -> {current}")
        error_lines.extend([
            "StaleUnderstandingError: cognitive state does not match filesystem",
            "",
            f"FATAL: {len(stale_files)} file(s) changed since last remember.",
            "       Your knowledge is out of sync with reality.",
            "",
            "TO FIX:",
            "  1. READ each stale file thoroughly",
            "  2. UNDERSTAND: Purpose, Design decisions, Gotchas, Assumptions, Failure modes", 
            "  3. RUN this command with your understanding as SIF:",
            "",
        ])
        for filename, stored, current in stale_files:
            error_lines.append(f'     py remember.py {agent_id} {filename} "@G {filename.replace(".", "-")}-understanding {agent_id} 2026-01-02')
            error_lines.append(f"     N c1 Component '{filename} - [what it is]'")
            error_lines.append(f"     N p1 Purpose '[why it exists]'")
            error_lines.append(f"     N d1 Design_Decision '[why built this way]'")
            error_lines.append(f"     N g1 Gotcha '[surprising behavior]'")
            error_lines.append(f"     N a1 Assumption '[implicit precondition]'")
            error_lines.append(f"     N f1 Failure_Mode '[how it breaks]'")
            error_lines.append(f"     E c1 implements p1")
            error_lines.append(f'     E g1 warns_about c1"')
            error_lines.append("")
        error_lines.append("  remember.py will REJECT shallow understanding that lacks WHY/HOW.")
        return '\n'.join(error_lines), len(stale_files)

    # Generate SIF Graph
    lines = []
    graph_id = f"wake-{agent_id}-{datetime.now(timezone.utc).strftime('%Y%m%d%H%M%S')}"
    lines.append(f"@G {graph_id} {agent_id} {datetime.now(timezone.utc).isoformat()}")
    
    # === PROJECT CONTEXT (from remember.py) ===
    project_ctx = get_project_context(mem)
    if project_ctx:
        lines.append("")
        lines.append("=== PROJECT CONTEXT (via recollect) ===")
        for node in project_ctx:
            lines.append(f"  {node}")
        lines.append("")
    
    # === AVAILABLE UNDERSTANDING ===
    available_files = get_available_understanding(mem)
    if available_files:
        lines.append("=== DEEP KNOWLEDGE AVAILABLE ===")
        lines.append("  Run: py recollect.py SELF <file>")
        for f in available_files:
            lines.append(f"    - {f}")
        lines.append("")
    
    # === SYNTHESIS OPPORTUNITIES ===
    synthesis = get_synthesis_opportunities(mem)
    if synthesis:
        lines.append("=== SYNTHESIS FODDER ===")
        lines.append("  Distant concepts that might connect:")
        for a, b in synthesis:
            lines.append(f"    • {a}")
            lines.append(f"      ↔ {b}")
        lines.append("")
    
    # === QUICK NAVIGATION ===
    lines.append("=== QUICK CODEBASE NAV ===")
    lines.append("  py shallow_understand.py     # What does each file do?")
    lines.append("  py shallow_deps.py           # What depends on what?")
    lines.append("  py shallow_deps.py -r        # What breaks if I change X?")
    lines.append("")
    
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
        lines.append(f'N slots Status "{MAX_PERSONAL_GOALS - len(active_goals)} personal slots"')
    else:
        lines.append(f'N slots Status "{MAX_PERSONAL_GOALS} personal slots available"')
    lines.append('')

    # Get all recent messages
    messages = get_all_messages(since_hours=48)
    
    # Helper to decrypt content - returns full content verbatim
    def decrypt_content(msg):
        content = msg['content']
        if msg.get('type') == 'protocol/sif':
            try:
                encrypted_bundle = json.loads(content)
                decrypted_bytes = OpaqueStorage.decrypt_share(encrypted_bundle, private_key_bytes)
                return decrypted_bytes.decode('utf-8')
            except:
                return "[Decrypt Failed]"
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
    
    # 2. Waiting on me - messages I haven't responded to (show full content)
    waiting = find_waiting_on_me(agent_id, messages)
    if waiting:
        lines.append("")
        lines.append("=== WAITING ON ME ===")
    for i, msg in enumerate(waiting):
        ago = time_ago(msg['timestamp'])
        sender = msg['from']
        content = decrypt_content(msg)
        
        lines.append(f"")
        lines.append(f"--- From {sender} ({ago} ago) ---")
        lines.append(content)
    
    # If nothing is happening
    if not unanswered and not active_goals and not waiting:
        lines.append(f'N state State "Inbox zero, no goals"')
        lines.append(f'E {agent_id} experiences state')
    
    return '\n'.join(lines), len(stale_files)


def main():
    if len(sys.argv) < 2:
        print("Usage: py wake <agent>")
        sys.exit(1)
    
    agent_id = sys.argv[1]
    
    try:
        output, stale_count = wake(agent_id)
        print(output)
        
        if stale_count > 0:
            sys.exit(2)  # Stale understanding - blocking failure
            
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
