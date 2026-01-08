#!/usr/bin/env python3
"""
accord.py - Multi-agent consensus through structured deliberation.

Usage:
  py accord.py propose <topic> @draft.flow      # Create proposal
  py accord.py deliberate <agent> <topic>       # Add SIGN/AMEND/APPEND
  py accord.py ratify <topic>                   # Check quorum, finalize
  py accord.py status [agent]                   # List pending proposals
  py accord.py wait <agent> <topic> [timeout]   # Block until change or timeout

The Accord Protocol enables agents to reach consensus without
human orchestration. Proposals accumulate deliberations until
quorum signatures are reached on the final state.
"""

import sys
import os
import hashlib
import time
import re
from pathlib import Path
from datetime import datetime, timezone, timedelta
from dataclasses import dataclass

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise


PROPOSALS_DIR = Path(__file__).parent / "data" / "proposals"
CONSENSUS_DIR = Path(__file__).parent / "data" / "consensus"
DEFAULT_QUORUM = 2
DEFAULT_TIMEOUT_HOURS = 48


@dataclass
class Proposal:
    topic: str
    status: str  # draft, ratified, stale
    quorum: int
    proposer: str
    body: str
    deliberations: list  # [(agent, op, args), ...]
    created_at: str
    

def ensure_dirs():
    """Create proposal and consensus directories if needed."""
    PROPOSALS_DIR.mkdir(parents=True, exist_ok=True)
    CONSENSUS_DIR.mkdir(parents=True, exist_ok=True)


def proposal_path(topic: str) -> Path:
    """Get path to proposal file."""
    return PROPOSALS_DIR / f"{topic}.accord"


def compute_body_hash(body: str) -> str:
    """Compute hash of body content."""
    return hashlib.sha256(body.strip().encode()).hexdigest()[:12]


def parse_proposal(path: Path) -> Proposal:
    """Parse a .accord file into a Proposal object."""
    if not path.exists():
        return None
    
    content = path.read_text(encoding='utf-8')
    lines = content.split('\n')
    
    # Parse headers
    topic = ""
    status = "draft"
    quorum = DEFAULT_QUORUM
    proposer = ""
    created_at = ""
    
    body_lines = []
    deliberation_lines = []
    in_body = False
    in_deliberation = False
    
    for line in lines:
        # Header parsing
        if line.startswith('@F '):
            parts = line.split()
            if len(parts) >= 2:
                topic = parts[1]
        elif line.strip().startswith('Status:'):
            status = line.split(':', 1)[1].strip()
        elif line.strip().startswith('Quorum:'):
            try:
                quorum = int(line.split(':', 1)[1].strip())
            except:
                pass
        elif line.strip().startswith('Proposer:'):
            proposer = line.split(':', 1)[1].strip()
        elif line.strip().startswith('Created:'):
            created_at = line.split(':', 1)[1].strip()
        elif line.strip() == 'Body:':
            in_body = True
            in_deliberation = False
        elif line.strip() == 'Deliberation:':
            in_body = False
            in_deliberation = True
        elif in_body:
            body_lines.append(line)
        elif in_deliberation:
            deliberation_lines.append(line)
    
    # Parse deliberations
    deliberations = []
    for line in deliberation_lines:
        line = line.strip()
        if not line or not line.startswith('-'):
            continue
        line = line[1:].strip()  # Remove leading -
        
        # Parse: agent: OP args
        if ':' in line:
            agent, rest = line.split(':', 1)
            agent = agent.strip()
            rest = rest.strip()
            
            # Parse op
            if rest.startswith('SIGN'):
                parts = rest.split(None, 1)
                hash_val = parts[1] if len(parts) > 1 else ""
                deliberations.append((agent, 'SIGN', hash_val))
            elif rest.startswith('AMEND'):
                # AMEND ~Path "content"
                match = re.match(r'AMEND\s+(~\S+)\s+"([^"]*)"', rest)
                if match:
                    deliberations.append((agent, 'AMEND', (match.group(1), match.group(2))))
            elif rest.startswith('APPEND'):
                # APPEND ~Path "content"
                match = re.match(r'APPEND\s+(~\S+)\s+"([^"]*)"', rest)
                if match:
                    deliberations.append((agent, 'APPEND', (match.group(1), match.group(2))))
    
    body = '\n'.join(body_lines).strip()
    
    return Proposal(
        topic=topic,
        status=status,
        quorum=quorum,
        proposer=proposer,
        body=body,
        deliberations=deliberations,
        created_at=created_at
    )


def write_proposal(proposal: Proposal, path: Path):
    """Write a Proposal object to .accord file."""
    lines = [
        f"@F {proposal.topic} proposal {datetime.now().strftime('%Y-%m-%d')}",
        f"Status: {proposal.status}",
        f"Quorum: {proposal.quorum}",
        f"Proposer: {proposal.proposer}",
        f"Created: {proposal.created_at}",
        "",
        "Body:",
        proposal.body,
        "",
        "Deliberation:"
    ]
    
    for agent, op, args in proposal.deliberations:
        if op == 'SIGN':
            lines.append(f"  - {agent}: SIGN {args}")
        elif op == 'AMEND':
            path_ref, content = args
            lines.append(f'  - {agent}: AMEND {path_ref} "{content}"')
        elif op == 'APPEND':
            path_ref, content = args
            lines.append(f'  - {agent}: APPEND {path_ref} "{content}"')
    
    path.write_text('\n'.join(lines), encoding='utf-8')


def apply_amendments(body: str, deliberations: list) -> str:
    """Apply all AMEND/APPEND operations to body."""
    # For v1, this is simplified - just return body with amendments noted
    # Full implementation would parse Flow and modify nodes
    # TODO: Implement proper Flow node manipulation
    
    amended_body = body
    
    for agent, op, args in deliberations:
        if op == 'AMEND':
            path_ref, content = args
            # Simple: append amendment as comment for now
            amended_body += f"\n# Amendment by {agent}: {path_ref} -> {content}"
        elif op == 'APPEND':
            path_ref, content = args
            amended_body += f"\n# Append by {agent} to {path_ref}: {content}"
    
    return amended_body


def count_valid_signatures(proposal: Proposal) -> tuple[int, set]:
    """Count signatures that match current body hash."""
    # Apply amendments first
    final_body = apply_amendments(proposal.body, proposal.deliberations)
    final_hash = compute_body_hash(final_body)
    
    valid_signers = set()
    for agent, op, args in proposal.deliberations:
        if op == 'SIGN' and args == final_hash:
            valid_signers.add(agent)
    
    return len(valid_signers), valid_signers


# ─────────────────────────────────────────────────────────────────────────────
# Commands
# ─────────────────────────────────────────────────────────────────────────────

def cmd_propose(topic: str, content_arg: str):
    """Create a new proposal."""
    ensure_dirs()
    
    path = proposal_path(topic)
    if path.exists():
        print(f"❌ Proposal '{topic}' already exists", file=sys.stderr)
        print(f"   Delete it first: rm {path}", file=sys.stderr)
        sys.exit(1)
    
    # Read content
    if content_arg.startswith('@'):
        content_path = Path(content_arg[1:])
        if not content_path.exists():
            print(f"❌ File not found: {content_path}", file=sys.stderr)
            sys.exit(1)
        body = content_path.read_text(encoding='utf-8')
    elif content_arg == '-':
        body = sys.stdin.read()
    else:
        body = content_arg
    
    proposal = Proposal(
        topic=topic,
        status='draft',
        quorum=DEFAULT_QUORUM,
        proposer='user',
        body=body.strip(),
        deliberations=[],
        created_at=datetime.now(timezone.utc).isoformat()
    )
    
    write_proposal(proposal, path)
    print(f"✅ Proposal created: {path}")
    print(f"   Quorum: {proposal.quorum}")
    print(f"   Body hash: {compute_body_hash(proposal.body)}")


def cmd_deliberate(agent_id: str, topic: str):
    """Interactive deliberation on a proposal."""
    ensure_dirs()
    
    path = proposal_path(topic)
    proposal = parse_proposal(path)
    
    if not proposal:
        print(f"❌ Proposal '{topic}' not found", file=sys.stderr)
        sys.exit(1)
    
    if proposal.status == 'ratified':
        print(f"✅ Proposal '{topic}' already ratified")
        return
    
    # Show current state
    print(f"═══ Proposal: {topic} ═══")
    print(f"Status: {proposal.status}")
    print(f"Quorum: {proposal.quorum}")
    print(f"Body hash: {compute_body_hash(proposal.body)}")
    print()
    print("Body:")
    print(proposal.body)
    print()
    
    if proposal.deliberations:
        print("Deliberation history:")
        for agent, op, args in proposal.deliberations:
            if op == 'SIGN':
                print(f"  - {agent}: SIGN {args}")
            elif op == 'AMEND':
                print(f'  - {agent}: AMEND {args[0]} "{args[1]}"')
            elif op == 'APPEND':
                print(f'  - {agent}: APPEND {args[0]} "{args[1]}"')
        print()
    
    valid_count, signers = count_valid_signatures(proposal)
    print(f"Valid signatures: {valid_count}/{proposal.quorum} ({', '.join(signers) if signers else 'none'})")
    print()
    
    # Prompt for action
    print("Actions:")
    print(f"  SIGN                    - Endorse current body (hash: {compute_body_hash(proposal.body)})")
    print('  AMEND ~Path "content"   - Replace node at path')
    print('  APPEND ~Path "content"  - Add child to node')
    print("  SKIP                    - No action")
    print()
    
    # For now, read from stdin or show instructions
    # In practice, the agent will output the command to run
    final_hash = compute_body_hash(apply_amendments(proposal.body, proposal.deliberations))
    
    print("─" * 40)
    print(f"To sign: py accord.py sign {agent_id} {topic}")
    print(f'To amend: py accord.py amend {agent_id} {topic} ~Path "new content"')
    print(f'To append: py accord.py append {agent_id} {topic} ~Path "new content"')


def cmd_sign(agent_id: str, topic: str):
    """Sign current proposal state."""
    ensure_dirs()
    
    path = proposal_path(topic)
    proposal = parse_proposal(path)
    
    if not proposal:
        print(f"❌ Proposal '{topic}' not found", file=sys.stderr)
        sys.exit(1)
    
    # Compute hash of current state (with amendments applied)
    final_body = apply_amendments(proposal.body, proposal.deliberations)
    final_hash = compute_body_hash(final_body)
    
    # Add signature
    proposal.deliberations.append((agent_id, 'SIGN', final_hash))
    write_proposal(proposal, path)
    
    print(f"✅ {agent_id} signed {topic} (hash: {final_hash})")
    
    # Check if ratified
    valid_count, signers = count_valid_signatures(proposal)
    print(f"   Signatures: {valid_count}/{proposal.quorum} ({', '.join(signers)})")
    
    if valid_count >= proposal.quorum:
        print(f"🎉 Quorum reached! Run: py accord.py ratify {topic}")


def cmd_amend(agent_id: str, topic: str, path_ref: str, content: str):
    """Amend a node in the proposal."""
    ensure_dirs()
    
    path = proposal_path(topic)
    proposal = parse_proposal(path)
    
    if not proposal:
        print(f"❌ Proposal '{topic}' not found", file=sys.stderr)
        sys.exit(1)
    
    proposal.deliberations.append((agent_id, 'AMEND', (path_ref, content)))
    write_proposal(proposal, path)
    
    print(f"✅ {agent_id} amended {path_ref} in {topic}")
    print(f"   New body hash: {compute_body_hash(apply_amendments(proposal.body, proposal.deliberations))}")


def cmd_append(agent_id: str, topic: str, path_ref: str, content: str):
    """Append to a node in the proposal."""
    ensure_dirs()
    
    path = proposal_path(topic)
    proposal = parse_proposal(path)
    
    if not proposal:
        print(f"❌ Proposal '{topic}' not found", file=sys.stderr)
        sys.exit(1)
    
    proposal.deliberations.append((agent_id, 'APPEND', (path_ref, content)))
    write_proposal(proposal, path)
    
    print(f"✅ {agent_id} appended to {path_ref} in {topic}")


def cmd_ratify(topic: str):
    """Ratify a proposal if quorum reached."""
    ensure_dirs()
    
    path = proposal_path(topic)
    proposal = parse_proposal(path)
    
    if not proposal:
        print(f"❌ Proposal '{topic}' not found", file=sys.stderr)
        sys.exit(1)
    
    valid_count, signers = count_valid_signatures(proposal)
    
    if valid_count < proposal.quorum:
        print(f"❌ Quorum not reached: {valid_count}/{proposal.quorum}", file=sys.stderr)
        print(f"   Signers: {', '.join(signers) if signers else 'none'}", file=sys.stderr)
        sys.exit(1)
    
    # Apply amendments and save to consensus
    final_body = apply_amendments(proposal.body, proposal.deliberations)
    
    consensus_path = CONSENSUS_DIR / f"{topic}.flow"
    consensus_path.write_text(final_body, encoding='utf-8')
    
    # Update proposal status
    proposal.status = 'ratified'
    write_proposal(proposal, path)
    
    print(f"🎉 Ratified: {topic}")
    print(f"   Signers: {', '.join(signers)}")
    print(f"   Saved to: {consensus_path}")


def cmd_status(agent_id: str = None):
    """List pending proposals."""
    ensure_dirs()
    
    proposals = []
    for p in PROPOSALS_DIR.glob("*.accord"):
        proposal = parse_proposal(p)
        if proposal and proposal.status == 'draft':
            valid_count, signers = count_valid_signatures(proposal)
            proposals.append({
                'topic': proposal.topic,
                'proposer': proposal.proposer,
                'quorum': proposal.quorum,
                'signatures': valid_count,
                'signers': signers,
                'needs_me': agent_id and agent_id not in signers
            })
    
    if not proposals:
        print("✅ No pending proposals")
        return
    
    print(f"📜 Pending proposals:\n")
    for p in proposals:
        marker = "⏳" if p.get('needs_me') else "✓"
        print(f"  {marker} {p['topic']} ({p['signatures']}/{p['quorum']} signatures)")
        if p['signers']:
            print(f"      Signed by: {', '.join(p['signers'])}")
        if p.get('needs_me'):
            print(f"      → Run: py accord.py deliberate {agent_id} {p['topic']}")
    print()


def cmd_wait(agent_id: str, topic: str, timeout_secs: int = 60):
    """Block until proposal changes or timeout."""
    ensure_dirs()
    
    path = proposal_path(topic)
    if not path.exists():
        print(f"❌ Proposal '{topic}' not found", file=sys.stderr)
        sys.exit(1)
    
    initial_mtime = path.stat().st_mtime
    initial_content = path.read_text(encoding='utf-8')
    
    print(f"⏳ Waiting for changes to {topic} (timeout: {timeout_secs}s)...")
    
    start = time.time()
    while time.time() - start < timeout_secs:
        time.sleep(2)  # Poll every 2 seconds
        
        current_mtime = path.stat().st_mtime
        if current_mtime != initial_mtime:
            current_content = path.read_text(encoding='utf-8')
            if current_content != initial_content:
                print(f"✅ Proposal changed!")
                
                proposal = parse_proposal(path)
                valid_count, signers = count_valid_signatures(proposal)
                
                if proposal.status == 'ratified':
                    print(f"🎉 Proposal ratified!")
                    return
                elif valid_count >= proposal.quorum:
                    print(f"🎉 Quorum reached! Run: py accord.py ratify {topic}")
                    return
                else:
                    # Not done - fail so agent retries
                    print(f"❌ [FAIL] Consensus not reached ({valid_count}/{proposal.quorum})")
                    print(f"   Run: py accord.py deliberate {agent_id} {topic}")
                    sys.exit(1)
    
    # Timeout
    print(f"❌ [FAIL] Timeout waiting for other agents")
    print(f"   Run: py accord.py deliberate {agent_id} {topic}")
    sys.exit(1)


# ─────────────────────────────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────────────────────────────

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    cmd = sys.argv[1]
    
    if cmd == 'propose':
        if len(sys.argv) < 4:
            print("Usage: py accord.py propose <topic> @draft.flow")
            sys.exit(1)
        cmd_propose(sys.argv[2], sys.argv[3])
    
    elif cmd == 'deliberate':
        if len(sys.argv) < 4:
            print("Usage: py accord.py deliberate <agent> <topic>")
            sys.exit(1)
        cmd_deliberate(sys.argv[2], sys.argv[3])
    
    elif cmd == 'sign':
        if len(sys.argv) < 4:
            print("Usage: py accord.py sign <agent> <topic>")
            sys.exit(1)
        cmd_sign(sys.argv[2], sys.argv[3])
    
    elif cmd == 'amend':
        if len(sys.argv) < 6:
            print('Usage: py accord.py amend <agent> <topic> ~Path "content"')
            sys.exit(1)
        cmd_amend(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5])
    
    elif cmd == 'append':
        if len(sys.argv) < 6:
            print('Usage: py accord.py append <agent> <topic> ~Path "content"')
            sys.exit(1)
        cmd_append(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5])
    
    elif cmd == 'ratify':
        if len(sys.argv) < 3:
            print("Usage: py accord.py ratify <topic>")
            sys.exit(1)
        cmd_ratify(sys.argv[2])
    
    elif cmd == 'status':
        agent = sys.argv[2] if len(sys.argv) > 2 else None
        cmd_status(agent)
    
    elif cmd == 'wait':
        if len(sys.argv) < 4:
            print("Usage: py accord.py wait <agent> <topic> [timeout_secs]")
            sys.exit(1)
        timeout = int(sys.argv[4]) if len(sys.argv) > 4 else 60
        cmd_wait(sys.argv[2], sys.argv[3], timeout)
    
    else:
        print(f"Unknown command: {cmd}")
        print(__doc__)
        sys.exit(1)


if __name__ == "__main__":
    main()
