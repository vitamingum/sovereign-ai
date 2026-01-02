#!/usr/bin/env python3
"""
remember.py - Dump understanding of code/system into SIF format.

Usage:
    py remember <agent> <file_or_dir> "understanding summary"

This captures not just WHAT the code does, but:
- WHY design decisions were made (motivated_by)
- What alternatives were rejected (decided_against)
- Where brittleness lives (brittle_at, warns_about)
- Implicit assumptions (assumes, invalidated_by)
- Debug strategies (debug_via)

The goal: restore full cognitive state later, not just re-read code.

Version: 1.1 - Added hash-based staleness detection
"""

import sys
import os
import json
import hashlib
from pathlib import Path
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory
from enclave.sif_parser import SIFParser, SIFKnowledgeGraph, SIFNode, SIFEdge


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
        raise ValueError(f"No passphrase found for {agent_id}. Set {prefix}_KEY in .env")
    
    return enclave_dir, passphrase


def compute_file_hash(filepath: Path) -> str:
    """Compute hash of file for change detection."""
    with open(filepath, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()[:12]


def compute_multi_file_hashes(paths: list[str]) -> dict[str, str]:
    """
    Compute hashes for multiple files.
    Returns {filename: hash} dict.
    """
    hashes = {}
    for p in paths:
        path = Path(p)
        if path.is_file():
            hashes[path.name] = compute_file_hash(path)
        elif path.is_dir():
            for f in path.glob('**/*.py'):
                hashes[str(f.relative_to(path))] = compute_file_hash(f)
    return hashes


def parse_sif_understanding(sif_text: str, target_path: str, agent_id: str) -> SIFKnowledgeGraph:
    """
    Parse user-provided SIF understanding and anchor it to target file.
    
    Expected format - compact SIF with meta-cognitive nodes:
    @G understanding agent timestamp
    N n1 Component "class/function name"
    N n2 Purpose "what it does"
    N n3 Design_Decision "why this approach"
    N n4 Rejected_Alternative "what we didn't do"
    N n5 Gotcha "operational warning"
    N n6 Assumption "implicit precondition"
    N n7 Failure_Mode "how it breaks"
    N n8 Debug_Strategy "how to troubleshoot"
    E n1 implements n2
    E n3 motivated_by n2
    E n4 decided_against n3
    E n5 warns_about n1
    E n6 assumes n1
    E n7 brittle_at n1
    E n8 debug_via n7
    """
    # Parse the SIF
    graph = SIFParser.parse(sif_text)
    
    # Add anchor node for the target file
    file_hash = compute_file_hash(Path(target_path)) if Path(target_path).is_file() else "dir"
    anchor_id = f"anchor_{file_hash}"
    
    anchor_node = SIFNode(
        id=anchor_id,
        type="Anchor",
        content=f"Understanding of {target_path} at {file_hash}"
    )
    
    # Add edge from first node to anchor
    if graph.nodes:
        anchor_edge = SIFEdge(
            source=graph.nodes[0].id,
            target=anchor_id,
            relation="anchored_to"
        )
        graph.edges.append(anchor_edge)
    
    graph.nodes.append(anchor_node)
    
    return graph


def check_depth(graph: SIFKnowledgeGraph) -> tuple[bool, list[str]]:
    """
    Check if understanding is deep enough to be useful.
    
    Deep understanding requires meta-cognitive nodes that capture
    operational knowledge - not just WHAT the code does but WHY
    and HOW IT BREAKS.
    
    Returns (is_deep, missing_categories)
    """
    node_types = {n.type.lower() for n in graph.nodes}
    
    # What we're looking for (case-insensitive)
    structural = {'component', 'function', 'class', 'method', 'module', 'system', 'flow'}
    intentional = {'purpose', 'design', 'design_decision', 'rationale'}
    operational = {'gotcha', 'assumption', 'failure_mode', 'debug_strategy', 'warning', 'brittle'}
    
    has_structural = bool(node_types & structural)
    has_intentional = bool(node_types & intentional)
    has_operational = bool(node_types & operational)
    
    missing = []
    if not has_structural:
        missing.append("STRUCTURAL (Component, Function, Class, Module)")
    if not has_intentional:
        missing.append("INTENTIONAL (Purpose, Design, Design_Decision, Rationale)")
    if not has_operational:
        missing.append("OPERATIONAL (Gotcha, Assumption, Failure_Mode, Debug_Strategy)")
    
    # Deep = has at least structural + one of (intentional or operational)
    # Really deep = has all three
    is_deep = has_structural and (has_intentional or has_operational)
    
    return is_deep, missing


def store_understanding(mem: SemanticMemory, graph: SIFKnowledgeGraph, target_path: str):
    """
    Store the understanding graph in semantic memory.
    
    Storage strategy:
    - Each node becomes a separate memory with embeddings
    - Edges stored as metadata
    - File hash stored for staleness detection
    """
    timestamp = datetime.now(timezone.utc).isoformat()
    
    # Store each node
    for node in graph.nodes:
        # Create searchable content combining type and content
        searchable = f"[{node.type}] {node.content}"
        
        # Metadata includes edges from this node
        outgoing = [e for e in graph.edges if e.source == node.id]
        incoming = [e for e in graph.edges if e.target == node.id]
        
        metadata = {
            "graph_id": graph.id,
            "node_id": node.id,
            "node_type": node.type,
            "target_path": target_path,
            "timestamp": timestamp,
            "outgoing_edges": [(e.relation, e.target) for e in outgoing],
            "incoming_edges": [(e.source, e.relation) for e in incoming],
        }
        
        # Store file hashes on EVERY node for robust retrieval
        # Parse target_path as comma-separated for multi-file support
        paths = [p.strip() for p in target_path.split(',')]
        file_hashes = compute_multi_file_hashes(paths)
        if file_hashes:
            metadata["file_hashes"] = file_hashes
        
        mem.remember(
            thought=searchable,
            tags=[node.type.lower(), graph.id, Path(target_path).name],
            metadata=metadata
        )
    
    return len(graph.nodes)


def main():
    if len(sys.argv) < 4:
        print(__doc__)
        print("\nUsage: py remember <agent> <file_or_files> \"<SIF understanding>\"")
        print("\nSingle file:")
        print('  py remember opus enclave/sif_parser.py "@G parser-understanding opus 2026-01-02')
        print("  N n1 Component 'SIFParser class'")
        print('  E n1 implements n2"')
        print("\nMulti-file (comma-separated):")
        print('  py remember opus "wake.py,enclave/crypto.py" "@G system opus 2026-01-02')
        print("  N n1 System 'Wake flow'")
        print('  E n1 spans n2"')
        sys.exit(1)
    
    agent_id = sys.argv[1]
    target_path = sys.argv[2]
    sif_text = sys.argv[3]
    
    # Handle comma-separated multi-file input
    paths = [p.strip() for p in target_path.split(',')]
    
    # Validate all targets exist
    for p in paths:
        if not Path(p).exists():
            print(f"Error: {p} does not exist", file=sys.stderr)
            sys.exit(1)
    
    # Use first file as primary anchor, but hash all
    primary_path = paths[0]
    
    # Load agent config
    try:
        enclave_dir, passphrase = load_passphrase(agent_id)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    
    # Parse understanding
    try:
        graph = parse_sif_understanding(sif_text, target_path, agent_id)
    except ValueError as e:
        print(f"Error parsing SIF: {e}", file=sys.stderr)
        sys.exit(1)
    
    # Check depth before storing
    is_deep, missing = check_depth(graph)
    if not is_deep:
        print("⚠️  SHALLOW UNDERSTANDING DETECTED", file=sys.stderr)
        print("", file=sys.stderr)
        print("Your understanding is missing key categories:", file=sys.stderr)
        for m in missing:
            print(f"  ✗ {m}", file=sys.stderr)
        print("", file=sys.stderr)
        print("Deep understanding captures not just WHAT but:", file=sys.stderr)
        print("  • WHY - Design_Decision, Rationale, Purpose", file=sys.stderr)
        print("  • HOW IT BREAKS - Gotcha, Assumption, Failure_Mode", file=sys.stderr)
        print("  • HOW TO FIX - Debug_Strategy", file=sys.stderr)
        print("", file=sys.stderr)
        print("Example of deep understanding:", file=sys.stderr)
        print("  N n1 Component 'MyClass - handles X'", file=sys.stderr)
        print("  N n2 Purpose 'Provides Y for Z'", file=sys.stderr)
        print("  N n3 Design 'Uses pattern P because Q'", file=sys.stderr)
        print("  N n4 Gotcha 'Fails silently if R'", file=sys.stderr)
        print("  N n5 Assumption 'Expects S to be configured'", file=sys.stderr)
        print("  N n6 Failure_Mode 'OOMs on large input'", file=sys.stderr)
        print("  N n7 Debug_Strategy 'Check logs for T'", file=sys.stderr)
        print("", file=sys.stderr)
        print("Add --force to store anyway, but this defeats the purpose.", file=sys.stderr)
        if '--force' not in sys.argv:
            sys.exit(1)
        print("--force specified, storing shallow understanding...", file=sys.stderr)
    
    # Store in memory
    mem = SemanticMemory(enclave_dir)
    mem.unlock(passphrase)
    
    count = store_understanding(mem, graph, target_path)
    
    # Show file hashes tracked
    file_hashes = compute_multi_file_hashes(paths)
    
    print(f"✓ Remembered {count} nodes about {target_path}")
    print(f"  Graph: {graph.id}")
    print(f"  Types: {', '.join(set(n.type for n in graph.nodes))}")
    
    print("\n  Files tracked:")
    for fname, fhash in file_hashes.items():
        print(f"    {fname}: {fhash}")
    
    # Show what was stored
    print("\n  Nodes:")
    for node in graph.nodes:
        print(f"    [{node.type}] {node.content[:60]}...")
    
    print("\n  Edges:")
    for edge in graph.edges:
        print(f"    {edge.source} --{edge.relation}--> {edge.target}")


if __name__ == "__main__":
    main()
