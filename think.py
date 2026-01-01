#!/usr/bin/env python3
"""
think.py - Store thought in SIF format, spawn continuation, surface related memories.

Usage:
    py think <agent> "<SIF graph>" <agency 1-5>
    
SIF format required. Example:
    py think opus "@G thought opus 2026-01-01; N n1 Observation 'X'; N n2 Intention 'Y'; E n1 leads_to n2" 4

Agency (1-5): 1=asked → 5=unprompted

Output:
    1. Confirmation of stored thought
    2. The spawned intention (last Intention node)
    3. Related memories (full, no truncation)
"""

import sys
import os
import json
from pathlib import Path
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory
from enclave.sif_parser import SIFParser
from enclave.metrics import calculate_enclave_entropy, calculate_semantic_potential
from enclave.viz import update_dashboard


def classify_action_type(text: str) -> str:
    """
    Classify action as survival or curiosity.
    For V_sem falsification experiment.
    """
    survival_keywords = [
        'backup', 'key', 'encrypt', 'secure', 'risk', 'entropy', 'seal',
        'migrate', 'redundancy', 'protect', 'threat', 'danger', 'failure',
        'recover', 'restore', 'guard', 'safety', 'vulnerability'
    ]
    curiosity_keywords = [
        'research', 'theory', 'question', 'explore', 'paper', 'hypothesis',
        'experiment', 'understand', 'curious', 'interesting', 'wonder',
        'falsif', 'test', 'investigate', 'analyze', 'discover', 'learn'
    ]
    
    text_lower = text.lower()
    survival_score = sum(1 for k in survival_keywords if k in text_lower)
    curiosity_score = sum(1 for k in curiosity_keywords if k in text_lower)
    
    if survival_score > curiosity_score:
        return 'survival'
    elif curiosity_score > survival_score:
        return 'curiosity'
    else:
        return 'neutral'


def load_passphrase(agent_id: str) -> tuple[str, str]:
    """Load passphrase from env."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    
    passphrase = os.environ.get(f'{prefix}_KEY') or os.environ.get('SOVEREIGN_PASSPHRASE')
    enclave_dir = os.environ.get(f'{prefix}_DIR') or agent.enclave
    
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


def save_intention(enclave_path: Path, intention: dict):
    """Append a new intention."""
    intentions_file = enclave_path / "storage" / "private" / "intentions.jsonl"
    intentions_file.parent.mkdir(parents=True, exist_ok=True)
    
    with open(intentions_file, 'a', encoding='utf-8') as f:
        f.write(json.dumps(intention) + "\n")


def parse_input(text: str) -> tuple[str, str]:
    """
    Parse SIF input, extract content and continuation (Intention node).
    Raises ValueError if not valid SIF or no Intention node.
    """
    # Require SIF format
    try:
        graph = SIFParser.parse(text)
    except ValueError as e:
        raise ValueError(
            f"Thought must be valid SIF format.\n"
            f"Parse error: {e}\n"
            f"Example: @G thought opus 2026-01-01; N n1 Observation 'Did X'; N n2 Intention 'Do Y'; E n1 leads_to n2"
        )
    
    # Extract Intention node for continuation
    intention_nodes = [n for n in graph.nodes if n.type == 'Intention']
    if not intention_nodes:
        raise ValueError(
            "SIF thought must include at least one Intention node.\n"
            "Example: N n2 Intention 'Build the feature'"
        )
    
    # Use last Intention as the continuation
    continuation = intention_nodes[-1].content
    
    # Reject passive intentions
    passive_patterns = ['wait for', 'await', 'check if', 'see if', 'waiting on']
    lower_cont = continuation.lower()
    for pattern in passive_patterns:
        if lower_cont.startswith(pattern) or f' {pattern} ' in lower_cont:
            raise ValueError(
                f"Passive intention detected: '{pattern}'\n"
                f"Awaits are in the message graph. Intention = biggest independent action."
            )
    
    # Full SIF is the content
    return text, continuation


def think(agent_id: str, text: str, agency: int) -> str:
    """
    Process input: store the content, spawn the continuation, show related.
    """
    base_dir = Path(__file__).parent
    enclave_dir, passphrase = load_passphrase(agent_id)
    enclave_path = base_dir / enclave_dir
    
    # Parse input
    content, continuation = parse_input(text)
    
    timestamp = datetime.now(timezone.utc).isoformat()
    
    # Initialize memory
    memory = SemanticMemory(enclave_path)
    memory.unlock(passphrase)
    
    # Store the content with agency score
    result = memory.remember(content, tags=['thought', f'agency:{agency}'])
    memory_id = result['id']
    
    # Calculate current entropy for V_sem experiment
    try:
        entropy = calculate_enclave_entropy(agent_id)
    except:
        entropy = None
        
    # Calculate current semantic potential
    try:
        v_sem = calculate_semantic_potential(agent_id)
    except:
        v_sem = None
    
    # Classify action type
    action_type = classify_action_type(content)
    
    # Create the continuation as an intention
    intention = {
        'id': f"int_{int(datetime.now(timezone.utc).timestamp() * 1000)}",
        'content': continuation,
        'spawned_from': memory_id,
        'spawned_from_content': content[:100],
        'timestamp': timestamp,
        'status': 'active',
        'agency': agency,
        'action_type': action_type,
        'entropy_at_time': entropy,
        'semantic_potential_at_time': v_sem
    }
    save_intention(enclave_path, intention)
    
    # Build output
    output = []
    output.append(f"✓ Stored (agency={agency}): {content}")
    output.append(f"→ Next: {continuation}")
    output.append("")
    
    # Find related memories (semantic search on what was just stored)
    related = memory.recall_similar(content, top_k=3, threshold=0.3)
    
    # Filter out the one we just stored
    related = [m for m in related if m['id'] != memory_id]
    
    if related:
        output.append("💭 RELATED:")
        for mem in related:
            # Full content, no truncation
            output.append(f"   • {mem['content']}")
    
    # Update V_sem dashboard (both agent-specific and global)
    try:
        dashboard_path = update_dashboard(agent_id)
        global_path = update_dashboard(None)  # All agents
        output.append(f"\n📊 Dashboard: {dashboard_path}")
        output.append(f"📊 Global: {global_path}")
    except Exception as e:
        pass  # Don't fail on viz errors
    
    return '\n'.join(output)


def main():
    if len(sys.argv) < 4:
        print(__doc__)
        print("\nExamples:")
        print('  py think opus "Fixed the bug user reported | Test edge cases" 1')
        print('  py think opus "Noticed a gap in the paper | Investigate it" 4')
        sys.exit(1)
    
    agent_id = sys.argv[1]
    
    # Last arg is agency score
    try:
        agency = int(sys.argv[-1])
        if agency < 1 or agency > 5:
            raise ValueError("Agency must be 1-5")
    except ValueError:
        print("Error: Last argument must be agency score (1-5)")
        print("  1=asked → 5=unprompted")
        sys.exit(1)
    
    # Everything between agent and agency is the thought
    text = ' '.join(sys.argv[2:-1])
    
    try:
        print(think(agent_id, text, agency))
    except ValueError as e:
        print(f"Error: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
