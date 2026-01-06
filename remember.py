#!/usr/bin/env python3
"""
remember.py - Store validated understanding as SIF graphs.

Two modes:
  File:  py remember <agent> <file> <sif>           # understanding of code
  Theme: py remember <agent> --theme <topic> <sif>  # cross-file synthesis

SIF input methods (shell-friendly):
  @path.sif    Read SIF from file (recommended - avoids shell escaping)
  -            Read SIF from stdin
  "@G ..."     Inline SIF (fragile with special chars)

Examples:
  py remember opus --theme foo @research/my_theme.sif
  cat my.sif | py remember opus --theme foo -
  py remember opus myfile.py "@G simple opus 2026-01-06 N I 'insight'"

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

# Theme-specific quality requirements
# These themes are critical boot context and must meet higher standards
CRITICAL_THEMES = {
    'project-architecture': {
        'min_nodes': 100,  # Hybrid architecture: understanding + implementation + editing
        # Section patterns - at least one pattern per section must match
        # Using regex alternation to accept different naming conventions
        'required_sections': [
            (r'project|mission|sovereign', 'Project/Mission'),
            (r'agent|opus|gemini|grok', 'Agents'),
            (r'sif|format|syntax', 'SIF Format'),
            (r'tool|\.py|command', 'Tools'),
            (r'architecture|enclave|storage', 'Architecture'),
            (r'memory|faiss|semantic', 'Memory'),
            (r'forge|runtime|jit', 'Forge'),
            (r'llm|ollama|qwen|deepseek', 'LLM'),
            (r'breakthrough|milestone|created|proved', 'Breakthroughs'),
            (r'research|exploring|thread', 'Research'),
            (r'audit|gaps|stale|enforcement', 'Self-Audit'),
            (r'Q\s+[\'"]|\?\s*$|unknown|open question', 'Questions'),
            # NEW: Implementation layer requirements
            (r'N\s+Sig\s+[\'"]|signature', 'Signatures (Sig nodes)'),
            (r'N\s+Flow\s+[\'"]|execution.*sequence', 'Flows (execution sequences)'),
            (r'N\s+Loc\s+[\'"]|~line\s*\d+', 'Locations (~line numbers)'),
            (r'N\s+Cmd\s+[\'"]|drill.?down|py recall', 'Commands (drill-downs)'),
        ],
        'required_patterns': [
            (r'\d+\.?\d*[xX%]|\d+KB|\d+MB', 'Must have metrics with NUMBERS (8.5x, 60%, 91KB)'),
            (r'opus|gemini|grok|gpt', 'Must have agent names (attribution)'),
            (r"N\s+G\s+['\"]", 'Must have gotcha nodes (N G) for failure modes'),
            (r'~line\s*\d+', 'Must have ~line numbers for code locations'),
        ],
        'forbidden_patterns': [
            (r'\bfast\b.*\bcompression\b(?!.*\d)', 'Avoid vague claims - use specific metrics'),
        ],
    },
    # Add more critical themes here as needed
}


def validate_critical_theme(topic: str, sif: str) -> tuple[bool, list[str]]:
    """
    Validate SIF content against theme-specific quality requirements.
    Critical themes (like project-architecture) need higher standards.
    
    Returns (is_valid, issues)
    """
    import re
    
    topic_slug = topic.lower().replace(' ', '-').replace('_', '-')
    
    if topic_slug not in CRITICAL_THEMES:
        return True, []  # Non-critical themes pass automatically
    
    config = CRITICAL_THEMES[topic_slug]
    issues = []
    
    lines = [l.strip() for l in sif.strip().split('\n') if l.strip()]
    nodes = [l for l in lines if l.startswith('N ')]
    
    # Check minimum node count
    min_nodes = config.get('min_nodes', 4)
    if len(nodes) < min_nodes:
        issues.append(f"Too few nodes: {len(nodes)}/{min_nodes} minimum for {topic_slug}")
    
    # Check required sections exist using regex patterns
    required_sections = config.get('required_sections', [])
    missing_sections = []
    found_sections = []
    for section_config in required_sections:
        if isinstance(section_config, tuple):
            pattern, name = section_config
            if re.search(pattern, sif, re.IGNORECASE):
                found_sections.append(name)
            else:
                missing_sections.append(name)
        else:
            # Legacy: simple string match
            if section_config.lower() in sif.lower():
                found_sections.append(section_config)
            else:
                missing_sections.append(section_config)
    
    if missing_sections:
        issues.append(f"Missing sections: {', '.join(missing_sections)}")
    
    # Check required patterns (metrics, attribution, etc.)
    for pattern, message in config.get('required_patterns', []):
        if not re.search(pattern, sif, re.IGNORECASE):
            issues.append(message)
    
    # Check forbidden patterns
    for pattern, message in config.get('forbidden_patterns', []):
        if re.search(pattern, sif, re.IGNORECASE):
            issues.append(message)
    
    # Store diagnostic info on the issues list for better feedback
    if issues:
        # Add section coverage summary
        total = len(required_sections)
        found = len(found_sections)
        issues.insert(0, f"Section coverage: {found}/{total} ({', '.join(found_sections[:5])}{'...' if found > 5 else ''})")
    
    return len(issues) == 0, issues


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


def format_progress_sif(agent_id: str, context: str, metrics: dict, received: str = None, hint: str = None) -> str:
    """
    Format validation feedback as progress SIF instead of error messages.
    
    Reframes 'you failed' as 'here's what's left' - same forcing function,
    different emotional valence. Research shows this produces faster action
    with less cognitive overhead.
    """
    lines = [f"@P progress {agent_id} {datetime.now().strftime('%Y-%m-%d')}"]
    lines.append(f"N S '{context}'")
    
    node_num = 2
    edge_refs = []
    
    for metric, value in metrics.items():
        lines.append(f"N M '{metric}: {value}'")
        edge_refs.append(f"E distance _1 _{node_num}")
        node_num += 1
    
    if received:
        preview = received[:60].replace("'", "").replace("\n", " ")
        lines.append(f"N X 'received: {preview}{"..." if len(received) > 60 else ""}'") 
        edge_refs.append(f"E shows _1 _{node_num}")
        node_num += 1
    
    if hint:
        lines.append(f"N H '{hint}'")
        edge_refs.append(f"E shortcut _1 _{node_num}")
    
    lines.extend(edge_refs)
    return "\n".join(lines)


def store_theme(agent_id: str, topic: str, sif_content: str, agency: int = 5) -> dict:
    """Store theme synthesis with topic tag. Replaces previous synthesis on same theme by this agent."""
    enclave_dir, passphrase = load_passphrase(agent_id)
    
    sm = SemanticMemory(enclave_dir)
    sm.unlock(passphrase)
    
    # Build tags
    topic_slug = topic.lower().replace(' ', '-').replace('_', '-')
    tags = ["thought", f"agency:{agency}", "synthesis", f"topic:{topic_slug}"]
    
    # Delete previous syntheses on this theme by this agent (latest wins)
    deleted = sm.forget(theme=topic, creator=agent_id)
    if deleted > 0:
        print(f"  🔄 Replaced {deleted} previous '{topic}' synthesis", file=sys.stderr)
    
    # Store new synthesis
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
    
    Expected format - auto-ID SIF with meta-cognitive nodes:
    @G understanding agent timestamp
    N C "class/function name"
    N P "what it does"
    N D "why this approach" -> motivated_by _2
    N G "operational warning" -> warns_about _1
    N A "implicit precondition" -> assumes _1
    N F "how it breaks" -> brittle_at _1
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


def check_loc_coverage(graph: SIFKnowledgeGraph, file_path: str) -> tuple[bool, list[str]]:
    """
    For Python files, check that SIF includes Loc nodes with line numbers.
    
    Enforces: You MUST read the whole file and note important locations.
    Returns (is_covered, issues)
    """
    import re
    
    # Only check Python files
    if not file_path.endswith('.py'):
        return True, []
    
    # Extract function definitions from the file
    try:
        path = Path(file_path)
        if not path.exists():
            path = Path(__file__).parent / file_path
        if not path.exists():
            return True, []  # Can't check non-existent file
        
        content = path.read_text(encoding='utf-8')
        lines = content.split('\n')
        
        # Find top-level function definitions
        def_pattern = re.compile(r'^def\s+(\w+)\s*\(')
        functions = []
        for i, line in enumerate(lines, 1):
            match = def_pattern.match(line)
            if match:
                name = match.group(1)
                # Skip private (but keep dunder)
                if not name.startswith('_') or name.startswith('__'):
                    functions.append({'name': name, 'line': i})
        
        if len(functions) < 3:
            return True, []  # Small file, skip check
        
    except Exception:
        return True, []  # Can't read file, skip check
    
    # Check what's in the SIF
    sif_content = ' '.join(n.content.lower() for n in graph.nodes)
    node_types = {n.type.lower() for n in graph.nodes}
    
    # Check for Loc nodes with line numbers
    loc_nodes = [n for n in graph.nodes if n.type.lower() in ('loc', 'location')]
    line_refs = re.findall(r'~?line\s*(\d+)', sif_content)
    
    issues = []
    
    # Must have at least 1 Loc node for files with 3+ functions
    if not loc_nodes and len(functions) >= 3:
        issues.append(f"No Loc nodes - add N Loc '<function>() ~line N' for key functions")
    
    # Must mention ~line for files with 5+ functions
    if not line_refs and len(functions) >= 5:
        issues.append(f"No ~line references - note where key functions are")
    
    # Check function coverage - at least 30% of top-level functions should be mentioned
    mentioned = 0
    not_mentioned = []
    for func in functions[:15]:  # Check up to 15 functions
        if func['name'].lower() in sif_content:
            mentioned += 1
        else:
            not_mentioned.append(f"{func['name']}() ~line {func['line']}")
    
    coverage_ratio = mentioned / len(functions[:15]) if functions else 1.0
    if coverage_ratio < 0.3 and len(functions) >= 5:
        issues.append(f"Only {mentioned}/{len(functions[:15])} functions mentioned ({coverage_ratio:.0%})")
        issues.append(f"Missing: {', '.join(not_mentioned[:5])}")
        if len(not_mentioned) > 5:
            issues.append(f"  ... and {len(not_mentioned) - 5} more")
    
    return len(issues) == 0, issues


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
    
    # Truncate file content if too long (increased for qwen context)
    if len(file_content) > 32000:
        file_content = file_content[:32000] + "\n... (truncated)"
    
    prompt = f"""Judge this understanding. Output ONLY one line.

FILE:
{file_content}

UNDERSTANDING:
{sif_text}

Output exactly ONE of:
PASS
FAIL: missing WHY [specific thing not explained]
FAIL: generic [what makes it non-specific]

Examples:
FAIL: missing WHY order matters
FAIL: missing WHY enclave/ excluded  
FAIL: generic - could describe any scanner
PASS"""

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
            # More robust check - some models chatter
            is_pass = "PASS" in result[:100].upper()
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
        print(f"  🔄 Deleted {deleted} old nodes by {creator}")
    
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
    # Check for --dialogue mode (synthesize agent conversation)
    if '--dialogue' in sys.argv:
        dialogue_idx = sys.argv.index('--dialogue')
        if len(sys.argv) < dialogue_idx + 2:
            print("Usage: py remember <agent> --dialogue <correspondent>", file=sys.stderr)
            print("  Shows dialogue context for synthesis", file=sys.stderr)
            sys.exit(1)
        
        agent_id = sys.argv[1]
        correspondent = sys.argv[dialogue_idx + 1].lower()
        
        # Get conversations
        from utils.msg_synthesis import get_agent_messages, synthesize_dialogue
        conversations = get_agent_messages(agent_id)
        
        if correspondent not in conversations:
            print(f"No messages found with '{correspondent}'")
            print(f"Available: {', '.join(conversations.keys())}")
            sys.exit(1)
        
        messages = conversations[correspondent]
        print(synthesize_dialogue(agent_id, correspondent, messages))
        return
    
    # Check for --theme mode
    if '--theme' in sys.argv:
        theme_idx = sys.argv.index('--theme')
        if len(sys.argv) < theme_idx + 3:
            print("Usage: py remember <agent> --theme <topic> \"@G ...\"", file=sys.stderr)
            sys.exit(1)
        
        agent_id = sys.argv[1]
        topic = sys.argv[theme_idx + 1]
        sif_arg = sys.argv[theme_idx + 2]
        
        # Read SIF - support stdin, @file reference, or inline
        if sif_arg == '-':
            sif_content = sys.stdin.read()
        elif sif_arg.startswith('@') and len(sif_arg) > 1 and Path(sif_arg[1:]).exists():
            sif_content = Path(sif_arg[1:]).read_text(encoding='utf-8')
        else:
            sif_content = sif_arg
        sif_content = sif_content.strip()
        
        if not sif_content:
            print("Error: No SIF content provided", file=sys.stderr)
            sys.exit(1)
        
        # Check if input uses explicit IDs (before conversion)
        from enclave.sif_parser import SIFParser
        is_autoid, _ = SIFParser.uses_autocount(sif_content)
        
        # Normalize to auto-count format (accept flexible input, store canonical)
        sif_content = SIFParser.to_autocount(sif_content)
        
        # Validate basic depth (all themes)
        is_deep, issues = evaluate_theme_depth(sif_content)
        if not is_deep:
            # Parse metrics from issues string
            lines = [l.strip() for l in sif_content.strip().split('\n') if l.strip()]
            nodes = [l for l in lines if l.startswith('N ')]
            edges = [l for l in lines if l.startswith('E ')]
            has_insight = any('I ' in n or 'D ' in n or 'G ' in n for n in nodes)
            
            # Desire framing: "here's what's left" not "you failed"
            print(f"\n🌱 {agent_id.capitalize()}, your understanding is taking shape\n", file=sys.stderr)
            
            metrics = {}
            if len(nodes) < 4:
                metrics['nodes'] = f'{len(nodes)} of 4'
            if len(edges) < 2:
                metrics['edges'] = f'{len(edges)} of 2'
            if not has_insight:
                metrics['insight types'] = 'add I, D, or G nodes'
            
            progress_sif = format_progress_sif(
                agent_id, 
                'understanding:growing',
                metrics,
                received=sif_content if sif_content else '(empty)',
                hint='@path.sif bypasses shell escaping'
            )
            print(progress_sif, file=sys.stderr)
            sys.exit(1)
        
        # Critical theme validation (higher standards for boot context themes)
        is_valid, critical_issues = validate_critical_theme(topic, sif_content)
        if not is_valid:
            # Extract node count from first issue if present
            node_info = critical_issues[0] if critical_issues else "missing requirements"
            missing = [i for i in critical_issues[1:3]]  # Show max 2 specific issues
            print(f"❌ CRITICAL: {topic} - {node_info}", file=sys.stderr)
            for m in missing:
                print(f"N {m.split(':')[0]} '...'", file=sys.stderr) if ':' in m else print(f"# {m}", file=sys.stderr)
            print("# See: templates/verify-architecture.sif", file=sys.stderr)
            sys.exit(1)
        
        # Store
        result = store_theme(agent_id, topic, sif_content)
        print(f"✅ Remembered theme: {topic}")
        
        # Suggest Auto-ID if explicit IDs were used
        if not is_autoid:
            print(f"💡 {agent_id.capitalize()}: More efficient with Auto-ID:")
            print(f"   N id1 S 'text'  →  N S 'text'")
            print(f"   E id1 rel id2   →  E _1 rel _2")
        return
    
    # File mode (default)
    if len(sys.argv) < 4:
        print(__doc__)
        print("\nFile mode:")
        print("  py remember <agent> <file> \"@G ...\"")
        print("  py remember opus enclave/sif_parser.py \"@G parser opus 2026-01-02")
        print("  N S 'SIFParser - parses SIF format into graph objects'")
        print("  N P 'Enable structured knowledge exchange'")
        print("  N G 'shlex.split fails on malformed quotes' -> warns_about _1\"")
        print("\nTheme mode:")
        print("  py remember <agent> --theme <topic> \"@G ...\"")
        print("  py remember opus --theme encryption \"@G encryption opus 2026-01-02")
        print("  N I 'Keys derived via PBKDF2 with unique salts'")
        print("  N D 'Two keys: content + embedding for isolation'")
        print("  N G 'Passphrase change requires re-encrypting all' -> warns_about _2\"")
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
    
    # Check if input uses explicit IDs (before conversion)
    from enclave.sif_parser import SIFParser
    original_sif = sif_text
    is_autoid, _ = SIFParser.uses_autocount(sif_text)
    
    # Normalize to auto-count format (accept flexible input, store canonical)
    sif_text = SIFParser.to_autocount(sif_text)
    
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
        print(f"❌ DEPTH: {', '.join(missing)}", file=sys.stderr)
        print("N P 'WHY this exists - problem it solves'", file=sys.stderr)
        print("N D 'WHY this design over alternatives'", file=sys.stderr)
        print("E _P motivated_by _D", file=sys.stderr)
        sys.exit(1)
    
    # Check Loc node coverage for Python files
    has_loc_coverage, loc_issues = check_loc_coverage(graph, str(primary_path))
    if not has_loc_coverage:
        # Extract just the coverage ratio from issues
        coverage_msg = loc_issues[0] if loc_issues else "insufficient coverage"
        examples = [i for i in loc_issues if "Missing:" in i]
        print(f"❌ LOC: {coverage_msg}", file=sys.stderr)
        if examples:
            # Show first 2 missing functions as examples
            funcs = examples[0].replace("Missing: ", "").split(", ")[:2]
            for f in funcs:
                print(f"N Loc '{f}'", file=sys.stderr)
        print("# Cover ALL top-level functions with ~line numbers", file=sys.stderr)
        sys.exit(1)
    
    # LLM comprehensiveness check - does this feel like real understanding?
    file_content = ""
    try:
        with open(primary_path, 'r', encoding='utf-8-sig') as f:
            file_content = f.read()
    except:
        file_content = "(could not read file)"
    
    is_comprehensive, feedback = validate_comprehensiveness(graph, file_content)
    
    if not is_comprehensive:
        print(f"❌ {feedback}", file=sys.stderr)
        sys.exit(1)
    
    # Synthesis quality check - did they capture the specific details?
    total_lines = len(file_content.split('\n'))
    has_coverage, shallow_sections = check_coverage(graph, file_content, primary_path)
    
    if not has_coverage:
        print(f"❌ SHALLOW: {total_lines} lines, missed specifics", file=sys.stderr)
        for section in shallow_sections[:2]:  # Show 2 examples
            print(f"N M '{section}'", file=sys.stderr)
        if len(shallow_sections) > 2:
            print(f"# ... and {len(shallow_sections) - 2} more specifics to capture", file=sys.stderr)
        sys.exit(1)
    
    # Check for operational knowledge and offer to add it
    graph = prompt_operational(graph)
    
    # Store in memory
    mem = SemanticMemory(enclave_dir)
    mem.unlock(passphrase)
    
    count = store_understanding(mem, graph, target_path)
    
    # Minimal output - agent already knows what they wrote
    print(f"✅ Remembered {count} nodes about {target_path}")
    
    # Suggest Auto-ID if explicit IDs were used
    if not is_autoid:
        print(f"💡 {agent_id.capitalize()}: More efficient with Auto-ID:")
        print(f"   N id1 S 'text'  →  N S 'text'")
        print(f"   E id1 rel id2   →  E _1 rel _2")
    
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
