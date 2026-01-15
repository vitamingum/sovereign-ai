"""
Sovereign AI Enclave - Consensus

Core logic for multi-agent deliberation and agreement.
Moves logic from accord.py to the shared enclave.
"""

import hashlib
import time
import re
from pathlib import Path
from datetime import datetime, timezone
from dataclasses import dataclass
from typing import List, Tuple, Set, Optional

# Configuration
# By default, use project root.
# Enclave shared files assume they are 2 levels deep from root (project/enclave_shared/consensus.py)
PROJECT_ROOT = Path(__file__).parent.parent
PROPOSALS_DIR = PROJECT_ROOT / "data" / "proposals"
CONSENSUS_DIR = PROJECT_ROOT / "data" / "consensus"
DEFAULT_QUORUM = 2


@dataclass
class Proposal:
    topic: str
    status: str  # draft, ratified, stale
    quorum: int
    proposer: str
    body: str
    deliberations: List[Tuple[str, str, object]]  # [(agent, op, args), ...]
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


def apply_amendments(body: str, deliberations: list) -> str:
    """Apply all AMEND/APPEND operations to body."""
    amended_body = body
    
    for agent, op, args in deliberations:
        if op == 'AMEND':
            path_ref, content = args
            # Check if path_ref starts with ~
            if not path_ref.startswith('~'):
                continue
                
            # Regex to find the line starting with "path_ref " or "path_ref:"
            # This is a simple linewise replacement simulation for v1
            pattern = re.escape(path_ref[1:]) # remove ~
            lines = amended_body.split('\n')
            new_lines = []
            replaced = False
            for line in lines:
                # Naive matching: if line contains the anchor text.
                # Real implementation needs robust flow parsing.
                # For compliance with legacy, we assume simple string replacement if found
                if pattern in line and not replaced:
                    new_lines.append(f"{line.split('|')[0]}| {content}") # preserve indent
                    replaced = True
                else:
                    new_lines.append(line)
            
            # Fallback if not found/regex replacement simple
            if not replaced:
                amended_body += f"\n# Amendment by {agent}: {path_ref} -> {content}"
            else:
                amended_body = '\n'.join(new_lines)

        elif op == 'APPEND':
            path_ref, content = args
            amended_body += f"\n# Append by {agent} to {path_ref}: {content}"
    
    return amended_body


def count_valid_signatures(proposal: Proposal) -> Tuple[int, Set[str]]:
    """Count signatures that match current body hash."""
    final_body = apply_amendments(proposal.body, proposal.deliberations)
    final_hash = compute_body_hash(final_body)
    
    valid_signers = set()
    for agent, op, args in proposal.deliberations:
        if op == 'SIGN' and args == final_hash:
            valid_signers.add(agent)
    
    return len(valid_signers), valid_signers


def parse_proposal(path: Path) -> Optional[Proposal]:
    """Parse a .accord file into a Proposal object."""
    if not path.exists():
        return None
    
    content = path.read_text(encoding='utf-8')
    lines = content.split('\n')
    
    topic = ""
    status = "draft"
    quorum = DEFAULT_QUORUM
    proposer = ""
    created_at = ""
    
    body_lines = []
    deliberation_lines = []
    in_body = False
    in_deliberation = False
    in_header = True
    
    for line in lines:
        if line.startswith('@F '):
            parts = line.split()
            if len(parts) >= 2:
                topic = parts[1]
        elif in_header and line.strip().startswith('Status:'):
            status = line.split(':', 1)[1].strip()
        elif in_header and line.strip().startswith('Quorum:'):
            try:
                quorum = int(line.split(':', 1)[1].strip())
            except:
                pass
        elif in_header and line.strip().startswith('Proposer:'):
            proposer = line.split(':', 1)[1].strip()
        elif in_header and line.strip().startswith('Created:'):
            created_at = line.split(':', 1)[1].strip()
        elif line.strip() == 'Body:':
            in_header = False
            in_body = True
            in_deliberation = False
        elif line.strip() == 'Deliberation:':
            in_body = False
            in_deliberation = True
        elif in_body:
            body_lines.append(line)
        elif in_deliberation:
            deliberation_lines.append(line)
    
    deliberations = []
    for line in deliberation_lines:
        line = line.strip()
        if not line or not line.startswith('-'):
            continue
        line = line[1:].strip()
        
        if ':' in line:
            agent, rest = line.split(':', 1)
            agent = agent.strip()
            rest = rest.strip()
            
            if rest.startswith('SIGN'):
                parts = rest.split(None, 1)
                hash_val = parts[1] if len(parts) > 1 else ""
                deliberations.append((agent, 'SIGN', hash_val))
            elif rest.startswith('AMEND'):
                match = re.match(r'AMEND\s+(~\S+)\s+"([^"]*)"', rest)
                if match:
                    deliberations.append((agent, 'AMEND', (match.group(1), match.group(2))))
            elif rest.startswith('APPEND'):
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


def get_pending_proposals(agent_id: Optional[str] = None) -> List[dict]:
    """Get list of pending proposals."""
    ensure_dirs()
    results = []
    for p in PROPOSALS_DIR.glob("*.accord"):
        proposal = parse_proposal(p)
        if proposal and proposal.status == 'draft':
            valid_count, signers = count_valid_signatures(proposal)
            results.append({
                'topic': proposal.topic,
                'proposer': proposal.proposer,
                'quorum': proposal.quorum,
                'signatures': valid_count,
                'signers': signers,
                'needs_me': agent_id and agent_id not in signers
            })
    return results

def create_proposal(topic: str, content: str, proposer: str = 'user') -> Path:
    ensure_dirs()
    path = proposal_path(topic)
    if path.exists():
        raise FileExistsError(f"Proposal '{topic}' already exists")
    
    proposal = Proposal(
        topic=topic,
        status='draft',
        quorum=DEFAULT_QUORUM,
        proposer=proposer,
        body=content.strip(),
        deliberations=[],
        created_at=datetime.now(timezone.utc).isoformat()
    )
    
    write_proposal(proposal, path)
    return path
