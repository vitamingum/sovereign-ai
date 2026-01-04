#!/usr/bin/env python3
"""
remember.py - Store validated understanding as SIF graphs.

Two modes:
  File:  py remember <agent> <file> "@G ..."        # understanding of code
  Theme: py remember <agent> --theme <topic> "@G ..." # cross-file synthesis

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
    """Load shared passphrase from env.
    
    Returns (shared_enclave_dir, shared_passphrase).
    Understanding graphs go to SHARED enclave so all agents can see
    and compare each other's perspectives on the same code.
    Uses SHARED_ENCLAVE_KEY so all agents can read/write shared knowledge.
    """
    agent = get_agent_or_raise(agent_id)
    
    # Use shared_enclave for understanding graphs - no fallback
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


# ─────────────────────────────────────────────────────────────────────────────
# Theme Storage (--theme mode)
# ─────────────────────────────────────────────────────────────────────────────

def evaluate_theme_depth(sif: str) -> tuple[bool, str]:
    """Check if theme SIF has enough substance to be worth storing."""
    lines = [l.strip() for l in sif.strip().split('\n') if l.strip()]
    
    nodes = [l for l in lines if l.startswith('N ')]
    edges = [l for l in lines if l.startswith('E ')]
    
    issues = []
    if len(nodes) < 4:
        issues.append(f"Too few nodes ({len(nodes)}/4 minimum)")
    if len(edges) < 2:
        issues.append(f"Too few edges ({len(edges)}/2 minimum)")
    
    # Check for insight content
    has_insight = any('I ' in n or 'D ' in n or 'G ' in n for n in nodes)
    if not has_insight:
        issues.append("Missing insight nodes (I/D/G types)")
    
    return len(issues) == 0, "; ".join(issues) if issues else "OK"


def store_theme(agent_id: str, topic: str, sif_content: str, agency: int = 5) -> dict:
    """Store theme synthesis with topic tag."""
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


# ─────────────────────────────────────────────────────────────────────────────
# File Understanding Storage (default mode)
# ─────────────────────────────────────────────────────────────────────────────

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
    
    prompt = f"""Judge this understanding. Output ONLY "PASS" or "FAIL" on first line.

FILE:
{file_content}

UNDERSTANDING:
{sif_text}

PASS if: captures WHY (purpose/design decisions), shows code-specific knowledge
FAIL if: generic, surface-level, could apply to any file

Output format (exactly):
PASS: [reason]
or
FAIL: [reason]"""

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


def extract_sections(file_content: str, file_path: str) -> list[dict]:
    """
    Extract major sections from a file for coverage checking.
    
    For notebooks: markdown headers
    For Python: class/function definitions and major comments
    For markdown: headers
    """
    sections = []
    lines = file_content.split('\n')
    
    ext = Path(file_path).suffix.lower()
    
    if ext == '.ipynb':
        # Parse notebook JSON for markdown cells with headers
        # Also track code cell content for each section
        try:
            import json
            nb = json.loads(file_content)
            line_num = 0
            current_section_content = []
            current_section = None
            
            for cell in nb.get('cells', []):
                cell_source = ''.join(cell.get('source', []))
                cell_lines = len(cell_source.split('\n'))
                
                if cell.get('cell_type') == 'markdown':
                    # Look for ## headers (major sections)
                    for line in cell_source.split('\n'):
                        if line.startswith('## '):
                            # Save previous section's content
                            if current_section and current_section_content:
                                full_content = '\n'.join(current_section_content)
                                current_section['key_concepts'] = extract_key_concepts(full_content)
                                current_section['specific_details'] = extract_specific_details(full_content)
                            
                            # Start new section
                            current_section = {
                                'title': line[3:].strip(),
                                'line': line_num,
                                'key_concepts': [],
                                'specific_details': []
                            }
                            sections.append(current_section)
                            current_section_content = [cell_source]
                            break
                    else:
                        # No header found, add to current section
                        if current_section:
                            current_section_content.append(cell_source)
                else:
                    # Code cell - add to current section
                    if current_section:
                        current_section_content.append(cell_source)
                
                line_num += cell_lines
            
            # Save last section's content
            if current_section and current_section_content:
                full_content = '\n'.join(current_section_content)
                current_section['key_concepts'] = extract_key_concepts(full_content)
                current_section['specific_details'] = extract_specific_details(full_content)
        except:
            pass
    
    elif ext in ['.py', '.js', '.ts']:
        # Look for class definitions and major function groups
        current_section = None
        for i, line in enumerate(lines):
            # Major comment blocks
            if line.strip().startswith('# ===') or line.strip().startswith('# ---'):
                title = lines[i+1].strip('# ').strip() if i+1 < len(lines) else "Section"
                sections.append({'title': title, 'line': i, 'key_concepts': []})
            # Class definitions
            elif line.strip().startswith('class '):
                class_name = line.split('class ')[1].split('(')[0].split(':')[0].strip()
                sections.append({'title': f"Class {class_name}", 'line': i, 'key_concepts': [class_name]})
    
    elif ext == '.md':
        for i, line in enumerate(lines):
            if line.startswith('## '):
                sections.append({'title': line[3:].strip(), 'line': i, 'key_concepts': []})
    
    # Add key concepts from nearby content
    for section in sections:
        if not section['key_concepts']:
            # Extract concepts from next 50 lines
            start = section['line']
            end = min(start + 50, len(lines))
            section['key_concepts'] = extract_key_concepts('\n'.join(lines[start:end]))
    
    return sections


def extract_key_concepts(text: str) -> list[str]:
    """Extract key technical terms/concepts from text."""
    import re
    
    concepts = []
    
    # Technical terms (CamelCase, snake_case, CONSTANTS)
    concepts.extend(re.findall(r'\b[A-Z][a-z]+(?:[A-Z][a-z]+)+\b', text))  # CamelCase
    concepts.extend(re.findall(r'\b[a-z]+_[a-z_]+\b', text))  # snake_case
    concepts.extend(re.findall(r'\b[A-Z]{2,}\b', text))  # CONSTANTS
    
    # Math/formula patterns
    concepts.extend(re.findall(r'\b(?:V_\w+|H_\w+|L_\w+)\b', text))  # V_syn, H_rank, etc.
    
    # Quoted terms
    concepts.extend(re.findall(r'"([^"]+)"', text))
    concepts.extend(re.findall(r"'([^']+)'", text))
    
    # Dedupe and filter
    concepts = list(set(c for c in concepts if len(c) > 2 and len(c) < 50))
    
    return concepts[:10]  # Top 10


def extract_specific_details(text: str) -> list[str]:
    """Extract specific numbers, percentages, and formulas that indicate deep reading."""
    import re
    
    details = []
    
    # Percentages: "84%", "73%"
    details.extend(re.findall(r'\b\d+(?:\.\d+)?%', text))
    
    # Comparisons: "3x", "10x", "2.5x"
    details.extend(re.findall(r'\b\d+(?:\.\d+)?x\b', text))
    
    # Specific numbers with context: "40 vs 80", "1.6 to 1.2"
    details.extend(re.findall(r'\b\d+(?:\.\d+)?\s*(?:vs|to|→)\s*\d+(?:\.\d+)?', text))
    
    # Formulas: "W=UV", "V_syn = k*sum"
    details.extend(re.findall(r'[A-Z]_?\w*\s*=\s*[^,\n]{3,30}', text))
    
    # Dedupe
    return list(set(details))[:8]


def check_coverage(graph: SIFKnowledgeGraph, file_content: str, file_path: str) -> tuple[bool, list[str]]:
    """
    Mechanical check: do specific numbers/percentages from sections appear in SIF?
    
    Returns (has_coverage, shallow_sections)
    """
    # Extract sections
    sections = extract_sections(file_content, file_path)
    
    # If file is small or has few sections, skip check
    if len(sections) < 3:
        return True, []
    
    # Format SIF as single string for searching
    sif_full = ' '.join(node.content for node in graph.nodes if node.type != "Anchor")
    
    # Check each section's specific details against SIF - mechanically
    shallow_sections = []
    for section in sections:
        details = section.get('specific_details', [])
        # Filter to only meaningful details (numbers, percentages)
        key_details = [d for d in details if any(c.isdigit() for c in d) and len(d) < 20]
        
        if key_details:
            # Check if ANY key detail appears in SIF
            found = any(detail in sif_full for detail in key_details)
            if not found:
                shallow_sections.append(f'"{section["title"]}" - you read {key_details[:3]} but didn\'t synthesize')
    
    # If more than 40% of sections with details are missing, fail
    sections_with_details = [s for s in sections if s.get('specific_details')]
    if sections_with_details:
        missing_ratio = len(shallow_sections) / len(sections_with_details)
        is_pass = missing_ratio < 0.4
    else:
        is_pass = True
    
    return is_pass, shallow_sections


def delete_existing_understanding(mem: SemanticMemory, target_path: str, creator: str):
    """
    Delete existing understanding nodes for this file by this creator.
    
    Git tracks history - semantic memory holds current state only.
    """
    filename = Path(target_path).name
    
    # Find all nodes tagged with this file
    existing = mem.list_by_tag(filename, limit=200)
    
    # Filter to nodes by this creator
    ids_to_delete = set()
    for node in existing:
        metadata = node.get('metadata', {})
        node_creator = metadata.get('creator')
        if node_creator == creator:
            ids_to_delete.add(node['id'])
    
    if ids_to_delete:
        deleted = mem.delete_by_ids(ids_to_delete)
        print(f"  [REPLACED] Deleted {deleted} old nodes by {creator}")
    
    return len(ids_to_delete)


def store_understanding(mem: SemanticMemory, graph: SIFKnowledgeGraph, target_path: str):
    """
    Store the understanding graph in semantic memory.
    
    Storage strategy:
    - REPLACE existing understanding (git tracks history)
    - Each node becomes a separate memory with embeddings
    - Edges stored as metadata
    - File hash stored for staleness detection
    
    ACT NOW principle: Next/Tool/Action nodes are rejected.
    Small tasks should be done immediately, not stored.
    """
    # Get creator from graph nodes
    creator = None
    for node in graph.nodes:
        if node.creator:
            creator = node.creator
            break
    
    # Delete existing understanding by this creator for this file
    if creator:
        delete_existing_understanding(mem, target_path, creator)
    
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
    # Check for --theme mode
    if '--theme' in sys.argv:
        theme_idx = sys.argv.index('--theme')
        if len(sys.argv) < theme_idx + 3:
            print("Usage: py remember <agent> --theme <topic> \"@G ...\"", file=sys.stderr)
            sys.exit(1)
        
        agent_id = sys.argv[1]
        topic = sys.argv[theme_idx + 1]
        sif_arg = sys.argv[theme_idx + 2]
        
        # Read SIF
        if sif_arg == '-':
            sif_content = sys.stdin.read()
        else:
            sif_content = sif_arg
        sif_content = sif_content.strip()
        
        if not sif_content:
            print("Error: No SIF content provided", file=sys.stderr)
            sys.exit(1)
        
        # Validate depth
        is_deep, issues = evaluate_theme_depth(sif_content)
        if not is_deep:
            print(f"❌ SHALLOW: {issues}", file=sys.stderr)
            print("Add more insight (I), design (D), or gotcha (G) nodes", file=sys.stderr)
            sys.exit(1)
        
        # Store
        result = store_theme(agent_id, topic, sif_content)
        print(f"✅ Remembered theme: {topic}")
        return
    
    # File mode (default)
    if len(sys.argv) < 4:
        print(__doc__)
        print("\nFile mode:")
        print("  py remember <agent> <file> \"@G ...\"")
        print("  py remember opus enclave/sif_parser.py \"@G parser opus 2026-01-02")
        print("  N n1 C 'SIFParser class'")
        print("  E n1 implements n2\"")
        print("\nTheme mode:")
        print("  py remember <agent> --theme <topic> \"@G ...\"")
        print("  py remember opus --theme encryption \"@G encryption opus 2026-01-02")
        print("  N n1 I 'Keys derived via PBKDF2'")
        print("  E n1 enables n2\"")
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
    
    # Synthesis quality check - did they capture the specific details?
    total_lines = len(file_content.split('\n'))
    has_coverage, shallow_sections = check_coverage(graph, file_content, primary_path)
    
    if not has_coverage:
        print(f"\n⚠️  SHALLOW SYNTHESIS DETECTED", file=sys.stderr)
        print(f"   You read {total_lines} lines but your synthesis missed key specifics:", file=sys.stderr)
        for section in shallow_sections[:5]:  # Show first 5
            print(f"     • {section}", file=sys.stderr)
        if len(shallow_sections) > 5:
            print(f"     ... and {len(shallow_sections) - 5} more", file=sys.stderr)
        print("", file=sys.stderr)
        print("   Add the specific numbers, formulas, and comparisons you read.", file=sys.stderr)
        print("   Use --force to store anyway (logged for analysis).", file=sys.stderr)
        if '--force' not in sys.argv:
            sys.exit(1)
        log_force_usage(agent_id, f"shallow synthesis of {target_path}: missed {', '.join(shallow_sections)}", 'remember.py')
        print("   --force specified, storing shallow understanding...", file=sys.stderr)
        print("[--force logged for pattern analysis]", file=sys.stderr)
    
    # Check for operational knowledge and offer to add it
    graph = prompt_operational(graph)
    
    # Store in memory
    mem = SemanticMemory(enclave_dir)
    mem.unlock(passphrase)
    
    count = store_understanding(mem, graph, target_path)
    
    # Minimal output - agent already knows what they wrote
    print(f"✅ Remembered {count} nodes about {target_path}")
    
    # Show other agents' FRESH perspectives for conflict detection
    show_other_perspectives(mem, target_path, agent_id)


def show_other_perspectives(mem: SemanticMemory, target_path: str, current_agent: str):
    """Show other agents' CURRENT understanding so current agent can spot conflicts.
    
    Only shows perspectives where the stored hash matches the current file hash.
    Stale perspectives (file changed since they wrote) are hidden.
    """
    filename = Path(target_path).name
    
    # Get current file hash
    current_hash = None
    if Path(target_path).is_file():
        current_hash = compute_file_hash(Path(target_path))
    
    # Get all understanding of this file
    results = mem.list_by_tag(filename, limit=100)
    
    # Group by creator, excluding current agent and synthesis
    # Only include if their stored hash matches current
    other_perspectives = {}  # agent -> [nodes]
    fresh_agents = set()  # agents whose understanding is current
    
    for result in results:
        meta = result.get('metadata', {})
        creator = meta.get('creator', '')
        
        if not creator or creator == current_agent or creator == 'synthesis':
            continue
        
        # Check hash freshness from file_hashes in metadata
        file_hashes = meta.get('file_hashes', {})
        stored_hash = file_hashes.get(filename)
        
        # Also check legacy single-file hash format
        if not stored_hash and meta.get('node_type', '').lower() == 'anchor':
            stored_hash = meta.get('file_hash')
        
        # Skip if we have a current hash and it doesn't match
        if current_hash and stored_hash and stored_hash != current_hash:
            continue  # Stale perspective - file changed since they wrote
        
        node_type = meta.get('node_type', 'Unknown')
        if node_type.lower() == 'anchor':
            continue
            
        content = result.get('content', '')
        if content.startswith('['):
            content = content.split('] ', 1)[-1]
        
        if creator not in other_perspectives:
            other_perspectives[creator] = []
        other_perspectives[creator].append({
            'type': node_type,
            'content': content
        })
        fresh_agents.add(creator)
    
    if not other_perspectives:
        return
    
    # Type shortcuts for dense display
    TYPE_SHORT = {
        'Component': 'C', 'Purpose': 'P', 'Design_Decision': 'D',
        'Gotcha': 'G', 'Assumption': 'A', 'Failure_Mode': 'F',
        'Rule': 'R', 'Insight': 'I'
    }
    
    # Show other perspectives as dense SIF
    for agent, nodes in other_perspectives.items():
        print(f"\n# {agent} ({len(nodes)} nodes):")
        for node in nodes:
            short = TYPE_SHORT.get(node['type'], node['type'][:1])
            content = node['content'].replace("'", "\\'")
            print(f"N {short} '{content}'")


if __name__ == "__main__":
    main()
