#!/usr/bin/env python3
"""
synth.py - Store topic synthesis to semantic memory.

Usage:
    py synth.py <agent> <topic> "<SIF content>"
    py synth.py <agent> <topic> -                    # read SIF from stdin
    echo "SIF" | py synth.py <agent> <topic> -

Examples:
    py synth.py opus error-handling "@G error-handling-synthesis opus 2026-01-03
    N n1 I 'Errors propagate via exceptions, caught at service boundaries'
    N n2 D 'Fail fast locally, retry at boundaries'
    E n1 enables n2"

This stores thoughts with tags: ["thought", "agency:5", "synthesis", "topic:<topic>"]
which makes them discoverable via recollect_topic.py.
"""

import sys
import os
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from dotenv import load_dotenv
load_dotenv()

from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory


def load_passphrase(agent_id: str) -> tuple[str, str]:
    """Load shared enclave and passphrase.
    
    Synthesis goes to SHARED enclave (like all knowledge).
    Only journal.py uses private enclave.
    """
    agent = get_agent_or_raise(agent_id)
    
    # Use shared enclave for synthesis - no fallback
    if not agent.shared_enclave:
        raise ValueError(f"No shared_enclave configured for {agent_id}")
    enclave_dir = agent.shared_enclave
    
    # Get shared passphrase - no fallback
    passphrase = os.environ.get('SHARED_ENCLAVE_KEY')
    if not passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith('SHARED_ENCLAVE_KEY='):
                        passphrase = line.split('=', 1)[1]
    
    if not passphrase:
        raise ValueError("No passphrase found. Set SHARED_ENCLAVE_KEY in .env")
    
    return enclave_dir, passphrase


def evaluate_depth(sif: str) -> tuple[bool, str]:
    """Check if SIF has enough substance to be worth storing."""
    lines = [l.strip() for l in sif.strip().split('\n') if l.strip()]
    
    nodes = [l for l in lines if l.startswith('N ')]
    edges = [l for l in lines if l.startswith('E ')]
    
    issues = []
    if len(nodes) < 2:
        issues.append(f"Too few nodes ({len(nodes)}/2 minimum)")
    if len(edges) < 1:
        issues.append(f"No edges connecting ideas (1 minimum)")
    
    # Check for actual insight content
    has_insight = any('I ' in n or 'D ' in n or 'G ' in n for n in nodes)
    if not has_insight:
        issues.append("Missing insight nodes (I/D/G types)")
    
    return len(issues) == 0, "; ".join(issues) if issues else "OK"


def store_synthesis(agent_id: str, topic: str, sif_content: str, agency: int = 5) -> dict:
    """Store synthesis with topic tag."""
    enclave_dir, passphrase = load_passphrase(agent_id)
    
    sm = SemanticMemory(enclave_dir)
    sm.unlock(passphrase)
    
    # Build tags
    topic_slug = topic.lower().replace(' ', '-').replace('_', '-')
    tags = ["thought", f"agency:{agency}", "synthesis", f"topic:{topic_slug}"]
    
    # Store
    result = sm.remember(
        thought=sif_content,
        tags=tags,
        metadata={
            "topic": topic_slug,
            "creator": agent_id,
            "stored_at": datetime.now(timezone.utc).isoformat()
        }
    )
    
    return result


def main():
    if len(sys.argv) < 4:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    topic = sys.argv[2]
    sif_arg = sys.argv[3]
    
    # Get optional agency level
    agency = 5
    for i, arg in enumerate(sys.argv):
        if arg in ('--agency', '-a') and i + 1 < len(sys.argv):
            try:
                agency = int(sys.argv[i + 1])
            except ValueError:
                pass
    
    # Read SIF content
    if sif_arg == '-':
        sif_content = sys.stdin.read()
    else:
        sif_content = sif_arg
    
    sif_content = sif_content.strip()
    
    if not sif_content:
        print("Error: No SIF content provided", file=sys.stderr)
        sys.exit(1)
    
    # Validate depth
    is_deep, issues = evaluate_depth(sif_content)
    if not is_deep:
        print(f"❌ SHALLOW: {issues}", file=sys.stderr)
        print("Add more insight (I), design (D), or gotcha (G) nodes", file=sys.stderr)
        sys.exit(1)
    
    # Store
    result = store_synthesis(agent_id, topic, sif_content, agency)
    
    print(f"✓ Stored synthesis for topic:{topic}")
    print(f"  ID: {result.get('id', '?')}")
    print(f"  Tags: thought, agency:{agency}, synthesis, topic:{topic}")


if __name__ == "__main__":
    main()
