#!/usr/bin/env python3
"""
remember.py - Store validated understanding of code as SIF graphs.

Usage:
    py remember <agent> <file_or_dir> "@G graph-name..."

Validates understanding depth before storing - rejects shallow descriptions
that only say WHAT without WHY. Captures:
- WHY design decisions were made (motivated_by)
- What alternatives were rejected (decided_against)  
- Where brittleness lives (brittle_at, warns_about)
- Implicit assumptions (assumes, invalidated_by)
- Debug strategies (debug_via)

The goal: restore full cognitive state later, not just re-read code.
Tracks file hashes for staleness detection.
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


def log_force_usage(agent_id: str, context: str, tool: str):
    """Log when --force is used for pattern analysis."""
    agent = get_agent_or_raise(agent_id)
    log_file = Path(agent.enclave) / "storage" / "private" / "force_log.jsonl"
    log_file.parent.mkdir(parents=True, exist_ok=True)
    
    entry = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "tool": tool,
        "context": context[:200]  # First 200 chars for brevity
    }
    with open(log_file, 'a', encoding='utf-8') as f:
        f.write(json.dumps(entry) + '\n')


def load_passphrase(agent_id: str) -> tuple[str, str]:
    """Load passphrase from env.
    
    Returns (shared_enclave_dir, passphrase).
    Understanding graphs go to SHARED enclave so all agents can see
    and compare each other's perspectives on the same code.
    """
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    
    passphrase = os.environ.get(f'{prefix}_KEY') or os.environ.get('SOVEREIGN_PASSPHRASE')
    # Use effective_enclave (shared if configured) for understanding graphs
    enclave_dir = os.environ.get(f'{prefix}_DIR') or agent.effective_enclave
    
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
    N n2 Purpose "what it does" creator=human
    N n3 Design_Decision "why this approach" creator=opus
    N n4 Rejected_Alternative "what we didn't do"
    N n5 Gotcha "operational warning"
    N n6 Assumption "implicit precondition"
    N n7 Failure_Mode "how it breaks"
    N n8 Debug_Strategy "how to troubleshoot"
    E n1 implements n2 creator=human
    E n3 motivated_by n2
    E n4 decided_against n3
    E n5 warns_about n1
    E n6 assumes n1
    E n7 brittle_at n1
    E n8 debug_via n7
    """
    # Parse the SIF
    graph = SIFParser.parse(sif_text)
    
    # Set default creator for nodes and edges that don't have one
    for node in graph.nodes:
        if node.creator == "unknown":
            node.creator = agent_id
    
    for edge in graph.edges:
        if edge.creator == "unknown":
            edge.creator = agent_id
    
    # Add anchor node for the target file
    file_hash = compute_file_hash(Path(target_path)) if Path(target_path).is_file() else "dir"
    anchor_id = f"anchor_{file_hash}"
    
    anchor_node = SIFNode(
        id=anchor_id,
        type="Anchor",
        content=f"Understanding of {target_path} at {file_hash}",
        creator=agent_id
    )
    
    # Add edge from first node to anchor
    if graph.nodes:
        anchor_edge = SIFEdge(
            source=graph.nodes[0].id,
            target=anchor_id,
            relation="anchored_to",
            creator=agent_id
        )
        graph.edges.append(anchor_edge)
    
    graph.nodes.append(anchor_node)
    
    return graph


def check_depth(graph: SIFKnowledgeGraph) -> tuple[bool, list[str]]:
    """
    Check if understanding is deep enough to be useful.
    
    Deep understanding is measured by graph richness:
    - Enough nodes to capture multiple aspects
    - Edges that connect ideas (not orphan nodes)
    - Variety in node types (not all Components)
    - At least some WHY knowledge (Purpose, Design, Rationale)
    
    Returns (is_deep, issues)
    """
    nodes = [n for n in graph.nodes if n.type != "Anchor"]
    edges = graph.edges
    node_types = {n.type.lower() for n in nodes}
    
    issues = []
    
    # Graph structure metrics
    if len(nodes) < 4:
        issues.append(f"Too few nodes ({len(nodes)}/4 minimum)")
    if len(edges) < 3:
        issues.append(f"Too few edges ({len(edges)}/3 minimum - connect your ideas)")
    if len(node_types) < 2:
        issues.append(f"Too few node types ({len(node_types)}/2 minimum - vary your analysis)")
    
    # Must have WHY knowledge, not just WHAT
    why_types = {'purpose', 'design', 'design_decision', 'rationale', 'why'}
    if not (node_types & why_types):
        issues.append("Missing WHY - add Purpose, Design, or Rationale nodes")
    
    is_deep = len(issues) == 0
    return is_deep, issues


def check_operational(graph: SIFKnowledgeGraph) -> tuple[bool, list[str]]:
    """
    Check if understanding includes operational knowledge.
    
    Operational knowledge captures WHERE-IT-BREAKS:
    - Gotcha: what surprises someone using this?
    - Assumption: what must be true for this to work?
    - Failure_Mode: how does this break?
    
    Returns (has_operational, missing_types)
    """
    nodes = [n for n in graph.nodes if n.type != "Anchor"]
    node_types = {n.type.lower() for n in nodes}
    
    operational_types = {'gotcha', 'assumption', 'failure_mode'}
    present = node_types & operational_types
    missing = operational_types - present
    
    return len(present) > 0, list(missing)


def prompt_operational(graph: SIFKnowledgeGraph) -> SIFKnowledgeGraph:
    """
    Interactive prompt to add operational knowledge if missing.
    
    Returns modified graph with any added nodes.
    """
    has_operational, missing = check_operational(graph)
    
    if has_operational:
        return graph  # Already has operational knowledge
    
    print("\n⚠️  No operational knowledge found (gotcha, assumption, failure_mode)")
    print("   Understanding has WHY but not WHERE-IT-BREAKS\n")
    print("[y] Proceed anyway")
    print("[n] Abort")
    print("[a] Add now - I'll prompt for each")
    
    try:
        choice = input("\nChoice [y/n/a]: ").strip().lower()
    except EOFError:
        # Non-interactive mode (pipe/redirect)
        return graph
    
    if choice == 'n':
        print("Aborted.")
        sys.exit(1)
    elif choice == 'a':
        # Find highest node ID number for new nodes
        max_id = 0
        for node in graph.nodes:
            if node.id.startswith('n') and node.id[1:].isdigit():
                max_id = max(max_id, int(node.id[1:]))
            elif node.id.startswith('g') and node.id[1:].isdigit():
                max_id = max(max_id, int(node.id[1:]))
            elif node.id.startswith('a') and node.id[1:].isdigit():
                max_id = max(max_id, int(node.id[1:]))
            elif node.id.startswith('f') and node.id[1:].isdigit():
                max_id = max(max_id, int(node.id[1:]))
        
        next_id = max_id + 1
        
        # Find the first Component or main node to link to
        target_node = None
        for node in graph.nodes:
            if node.type.lower() in ('component', 'function', 'class', 'module'):
                target_node = node.id
                break
        if not target_node and graph.nodes:
            target_node = graph.nodes[0].id
        
        print("\n(Press Enter to skip any)\n")
        
        # Gotcha
        gotcha = input("Gotcha (what surprises someone using this?): ").strip()
        if gotcha:
            gid = f"g{next_id}"
            graph.nodes.append(SIFNode(id=gid, type="Gotcha", content=gotcha))
            if target_node:
                graph.edges.append(SIFEdge(source=gid, target=target_node, relation="warns_about"))
            next_id += 1
            print(f"  Added: N {gid} Gotcha '{gotcha}'")
        
        # Assumption
        assumption = input("Assumption (what must be true for this to work?): ").strip()
        if assumption:
            aid = f"a{next_id}"
            graph.nodes.append(SIFNode(id=aid, type="Assumption", content=assumption))
            if target_node:
                graph.edges.append(SIFEdge(source=aid, target=target_node, relation="assumed_by"))
            next_id += 1
            print(f"  Added: N {aid} Assumption '{assumption}'")
        
        # Failure_Mode
        failure = input("Failure_Mode (how does this break?): ").strip()
        if failure:
            fid = f"f{next_id}"
            graph.nodes.append(SIFNode(id=fid, type="Failure_Mode", content=failure))
            if target_node:
                graph.edges.append(SIFEdge(source=fid, target=target_node, relation="breaks"))
            next_id += 1
            print(f"  Added: N {fid} Failure_Mode '{failure}'")
        
        if not (gotcha or assumption or failure):
            print("  No operational knowledge added.")
    
    return graph


def validate_comprehensiveness(graph: SIFKnowledgeGraph, file_content: str) -> tuple[bool, str]:
    """
    Use local LLM to validate understanding feels comprehensive.
    
    Returns (is_comprehensive, feedback)
    """
    import requests
    
    OLLAMA_URL = "http://localhost:11434/api/generate"
    
    # Format the SIF for the prompt
    sif_summary = []
    for node in graph.nodes:
        if node.type != "Anchor":
            sif_summary.append(f"[{node.type}] {node.content}")
    sif_text = '\n'.join(sif_summary)
    
    # Truncate file content if too long
    if len(file_content) > 6000:
        file_content = file_content[:6000] + "\n... (truncated)"
    
    prompt = f"""You are validating whether someone truly understood a file or just skimmed it.

FILE CONTENT:
{file_content}

THEIR UNDERSTANDING:
{sif_text}

Judge this understanding. A GOOD understanding:
1. Captures the core PURPOSE (why this exists)
2. Notes key DESIGN DECISIONS (why built this way, not another)
3. Shows specific knowledge from reading the ACTUAL code
4. Connects ideas with meaningful relationships

A BAD understanding:
1. Just restates the filename or obvious surface info
2. Generic descriptions that could apply to any file
3. Missing the WHY - only describes WHAT
4. Orphan facts with no connections

Note: Gotchas/assumptions/failure modes are VALUABLE when genuine, but don't require them.
Forced gotchas like "could fail if disk full" add noise.

Respond with EXACTLY one of:
PASS: [one sentence why this shows real understanding]
FAIL: [one sentence what's missing or superficial]"""

    try:
        response = requests.post(
            OLLAMA_URL,
            json={
                "model": "qwen2.5:7b",
                "prompt": prompt,
                "stream": False,
                "options": {"temperature": 0.1}
            },
            timeout=60
        )
        
        if response.status_code == 200:
            result = response.json().get("response", "").strip()
            is_pass = result.upper().startswith("PASS")
            return is_pass, result
        else:
            return True, f"(LLM unavailable: {response.status_code})"
            
    except requests.exceptions.ConnectionError:
        return True, "(Ollama not running - skipping comprehensiveness check)"
    except Exception as e:
        return True, f"(LLM error: {e})"


def store_understanding(mem: SemanticMemory, graph: SIFKnowledgeGraph, target_path: str):
    """
    Store the understanding graph in semantic memory.
    
    Storage strategy:
    - Each node becomes a separate memory with embeddings
    - Edges stored as metadata
    - File hash stored for staleness detection
    
    ACT NOW principle: Next/Tool/Action nodes are rejected.
    Small tasks should be done immediately, not stored.
    """
    timestamp = datetime.now(timezone.utc).isoformat()
    
    # ACT NOW: reject action-like nodes
    REJECTED_TYPES = {'next', 'tool', 'action', 'todo'}
    
    stored_count = 0
    for node in graph.nodes:
        # Skip action-like nodes - these should be done, not stored
        if node.type.lower() in REJECTED_TYPES:
            print(f"  [SKIPPED] {node.type} node - ACT NOW, don't store actions")
            continue
            
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
            "creator": node.creator,
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
        stored_count += 1
    
    return stored_count


def main():
    if len(sys.argv) < 4:
        print(__doc__)
        print("\nUsage: py remember <agent> <file_or_files> \"<SIF understanding>\"")
        print("       py remember <agent> <file_or_files> @path/to/understanding.sif")
        print("       py remember <agent> <file_or_files> -    # read SIF from stdin")
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
    sif_arg = sys.argv[3]
    # Windows CLI + shells can struggle with multi-line arguments.
    # Support '@file' to load Compact/JSON SIF from disk, and '-' for stdin.
    if sif_arg == '-':
        sif_text = sys.stdin.read()
    elif sif_arg.startswith('@') and len(sif_arg) > 1 and Path(sif_arg[1:]).exists():
        sif_text = Path(sif_arg[1:]).read_text(encoding='utf-8')
    else:
        sif_text = sif_arg
    
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
        print("Graph structure issues:", file=sys.stderr)
        for m in missing:
            print(f"  ✗ {m}", file=sys.stderr)
        print("", file=sys.stderr)
        print("Deep understanding needs:", file=sys.stderr)
        print("  • 4+ nodes - capture multiple aspects", file=sys.stderr)
        print("  • 3+ edges - connect your ideas", file=sys.stderr)
        print("  • 2+ node types - vary your analysis", file=sys.stderr)
        print("  • WHY nodes - Purpose, Design, Rationale", file=sys.stderr)
        print("", file=sys.stderr)
        print("Example of deep understanding:", file=sys.stderr)
        print("  N n1 Component 'MyClass - handles X'", file=sys.stderr)
        print("  N n2 Purpose 'Provides Y for Z'", file=sys.stderr)
        print("  N n3 Design 'Uses pattern P because Q'", file=sys.stderr)
        print("  N n4 Rationale 'Chose P over Alt because R'", file=sys.stderr)
        print("  E n1 implements n2", file=sys.stderr)
        print("  E n3 motivates n1", file=sys.stderr)
        print("  E n4 justifies n3", file=sys.stderr)
        print("", file=sys.stderr)
        print("Gotchas/Assumptions/Failure_Modes are valuable when GENUINE,", file=sys.stderr)
        print("but not required. Don't force them.", file=sys.stderr)
        print("", file=sys.stderr)
        print("Add --force to store anyway, but this defeats the purpose.", file=sys.stderr)
        if '--force' not in sys.argv:
            sys.exit(1)
        log_force_usage(agent_id, f"shallow understanding of {target_path}: missing {', '.join(missing)}", 'remember.py')
        print("--force specified, storing shallow understanding...", file=sys.stderr)
        print("[--force logged for pattern analysis]", file=sys.stderr)
    
    # LLM comprehensiveness check - does this feel like real understanding?
    file_content = ""
    try:
        with open(primary_path, 'r', encoding='utf-8-sig') as f:
            file_content = f.read()
    except:
        file_content = "(could not read file)"
    
    is_comprehensive, feedback = validate_comprehensiveness(graph, file_content)
    
    if not is_comprehensive:
        print("\n❌ Understanding seems superficial.", file=sys.stderr)
        print("   Add more depth - WHY decisions were made, WHAT breaks.", file=sys.stderr)
        if '--force' not in sys.argv:
            sys.exit(1)
        log_force_usage(agent_id, f"superficial understanding of {target_path}: {feedback}", 'remember.py')
        print("   --force specified, storing anyway...", file=sys.stderr)
        print("[--force logged for pattern analysis]", file=sys.stderr)
    
    # Check for operational knowledge and offer to add it
    graph = prompt_operational(graph)
    
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
