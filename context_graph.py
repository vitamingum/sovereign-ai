#!/usr/bin/env python3
"""
context_graph.py - Unified graph traversal across all synthesis levels.

The entire project is one SIF graph:
- Files (Level 0)
- Instant understanding (Level 1) 
- Structural deps (Level 2)
- Thoughts (Level 3)
- File understanding (Level 4)
- Topic synthesis (Level 5)

This tool builds and traverses "synthesis paths" to gather
comprehensive context before starting work on any file.

Usage:
    python context_graph.py opus sif_parser.py      # Context for a file
    python context_graph.py opus "messaging"        # Context for a topic
    python context_graph.py opus --build            # Build full graph
"""

import sys
import os
import json
import hashlib
from pathlib import Path
from collections import defaultdict
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory
from shallow_understand import instant_understand


# ─────────────────────────────────────────────────────────────────────────────
# The Unified Node Types
# ─────────────────────────────────────────────────────────────────────────────

class NodeType:
    FILE = "File"              # Level 0: raw artifact
    INSTANT = "Instant"        # Level 1: docstring extraction
    STRUCTURE = "Structure"    # Level 2: imports/exports
    THOUGHT = "Thought"        # Level 3: observations
    UNDERSTANDING = "Understanding"  # Level 4: WHY knowledge
    SYNTHESIS = "Synthesis"    # Level 5: cross-cutting beliefs


# ─────────────────────────────────────────────────────────────────────────────
# Graph Building
# ─────────────────────────────────────────────────────────────────────────────

def load_passphrase(agent_id: str) -> tuple[str, str]:
    """Load passphrase from env."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    
    passphrase = os.environ.get(f'{prefix}_KEY')
    enclave_dir = agent.enclave
    
    if not passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith(f'{prefix}_KEY='):
                        passphrase = line.split('=', 1)[1]
    
    return enclave_dir, passphrase


def get_file_imports(filepath: Path) -> list[str]:
    """Extract imports from a Python file."""
    if not filepath.exists() or filepath.suffix != '.py':
        return []
    
    imports = []
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if line.startswith('import '):
                    # import foo, bar
                    parts = line[7:].split(',')
                    for p in parts:
                        imports.append(p.strip().split()[0])
                elif line.startswith('from '):
                    # from foo import bar
                    parts = line[5:].split(' import ')
                    if parts:
                        imports.append(parts[0].strip())
    except:
        pass
    return imports


def build_unified_graph(agent_id: str) -> dict:
    """
    Build the complete unified graph across all synthesis levels.
    
    Returns {
        'nodes': {node_id: {type, content, level, ...}},
        'edges': [(source, relation, target), ...],
        'by_level': {level: [node_ids]},
        'by_file': {filename: [related_node_ids]}
    }
    """
    root = Path(__file__).parent
    enclave_dir, passphrase = load_passphrase(agent_id)
    
    nodes = {}
    edges = []
    by_level = defaultdict(list)
    by_file = defaultdict(list)
    
    # ─── LEVEL 0: Files ───
    files = {}
    for p in root.glob('*.py'):
        if not p.name.startswith(('generated_', 'test_', 'debug_')):
            files[p.name] = p
    
    enclave = root / 'enclave'
    if enclave.exists():
        for p in enclave.glob('*.py'):
            if not p.name.startswith('test'):
                files[f"enclave/{p.name}"] = p
    
    for filename, filepath in files.items():
        node_id = f"file:{filename}"
        nodes[node_id] = {
            'type': NodeType.FILE,
            'level': 0,
            'content': filename,
            'path': str(filepath)
        }
        by_level[0].append(node_id)
        by_file[filename].append(node_id)
        
        # File → File edges (imports)
        imports = get_file_imports(filepath)
        for imp in imports:
            # Map import to local file if possible
            if imp.startswith('enclave.'):
                target = f"enclave/{imp.split('.')[-1]}.py"
            elif imp in files or f"{imp}.py" in files:
                target = f"{imp}.py" if not imp.endswith('.py') else imp
            else:
                continue
            
            if target in files:
                edges.append((node_id, 'imports', f"file:{target}"))
    
    # ─── LEVEL 1: Instant Understanding ───
    for filename, filepath in files.items():
        if filepath.suffix == '.py':
            purpose, funcs = instant_understand(str(filepath))
            if purpose:
                inst_id = f"instant:{filename}"
                nodes[inst_id] = {
                    'type': NodeType.INSTANT,
                    'level': 1,
                    'content': purpose,
                    'functions': funcs[:5]
                }
                by_level[1].append(inst_id)
                by_file[filename].append(inst_id)
                edges.append((f"file:{filename}", 'has_instant', inst_id))
    
    # ─── LEVELS 3-5: From Semantic Memory ───
    if passphrase:
        memory = SemanticMemory(enclave_dir)
        memory.unlock(passphrase)
        
        all_mems = memory.list_all(limit=2000)
        
        for mem in all_mems:
            mem_id = mem.get('id', hashlib.md5(mem.get('content', '').encode()).hexdigest()[:8])
            content = mem.get('content', '')
            tags = mem.get('tags', [])
            meta = mem.get('metadata', {})
            
            # Determine level from tags/metadata
            if 'synthesis' in tags:
                level = 5
                node_type = NodeType.SYNTHESIS
            elif meta.get('target_path'):
                level = 4
                node_type = NodeType.UNDERSTANDING
            elif 'thought' in tags:
                level = 3
                node_type = NodeType.THOUGHT
            else:
                continue  # Skip unclassified
            
            node_id = f"{node_type.lower()}:{mem_id}"
            
            # Extract topic from tags for syntheses
            topic_slug = ''
            for tag in tags:
                if tag.startswith('topic:'):
                    topic_slug = tag[6:]
                    break
            
            nodes[node_id] = {
                'type': node_type,
                'level': level,
                'content': content[:500],
                'tags': tags,
                'topic': topic_slug,
                'graph_id': meta.get('graph_id', '')
            }
            by_level[level].append(node_id)
            
            # Link to file if has target_path
            target = meta.get('target_path', '')
            if target:
                filename = Path(target).name
                by_file[filename].append(node_id)
                if f"file:{filename}" in nodes:
                    edges.append((f"file:{filename}", 'has_understanding', node_id))
    
    # Second pass: connect thoughts to syntheses by topic mention
    for node_id, node in nodes.items():
        if node.get('type') == NodeType.THOUGHT:
            content_lower = node.get('content', '').lower()
            for synth_id, synth_node in nodes.items():
                if synth_node.get('type') == NodeType.SYNTHESIS:
                    topic = synth_node.get('topic', '')
                    if topic and topic.replace('-', ' ') in content_lower:
                        edges.append((node_id, 'contributes_to', synth_id))
        
        # Also connect syntheses to files they mention
        if node.get('type') == NodeType.SYNTHESIS:
            content_lower = node.get('content', '').lower()
            for filename in files.keys():
                name_base = filename.replace('.py', '').replace('enclave/', '')
                if name_base in content_lower:
                    edges.append((node_id, 'grounded_in', f"file:{filename}"))
    
    return {
        'nodes': nodes,
        'edges': edges,
        'by_level': dict(by_level),
        'by_file': dict(by_file)
    }


# ─────────────────────────────────────────────────────────────────────────────
# Synthesis Path Traversal
# ─────────────────────────────────────────────────────────────────────────────

def traverse_synthesis_path(graph: dict, start: str, max_hops: int = 3) -> dict:
    """
    Traverse from a starting point, following edges upward through synthesis levels.
    
    Returns nodes reachable within max_hops, organized by level.
    """
    nodes = graph['nodes']
    edges = graph['edges']
    
    # Build adjacency for bidirectional traversal
    adj = defaultdict(list)
    for src, rel, tgt in edges:
        adj[src].append((rel, tgt))
        adj[tgt].append((f"inv_{rel}", src))  # Inverse edge
    
    # BFS from start
    visited = {start: 0}
    queue = [(start, 0)]
    paths = {start: []}
    
    while queue:
        current, depth = queue.pop(0)
        if depth >= max_hops:
            continue
        
        for rel, neighbor in adj.get(current, []):
            if neighbor not in visited:
                visited[neighbor] = depth + 1
                paths[neighbor] = paths[current] + [(rel, current)]
                queue.append((neighbor, depth + 1))
    
    # Organize by level
    by_level = defaultdict(list)
    for node_id, hops in visited.items():
        node = nodes.get(node_id, {})
        level = node.get('level', -1)
        by_level[level].append({
            'id': node_id,
            'hops': hops,
            'type': node.get('type'),
            'content': node.get('content', '')[:200],
            'path': paths.get(node_id, [])
        })
    
    return dict(by_level)


def get_context_for_file(agent_id: str, filename: str) -> str:
    """
    Get comprehensive context before working on a file.
    
    Traverses synthesis paths to gather:
    - Direct understanding of this file
    - Related files (imports/imported by)
    - Thoughts mentioning this file
    - Topic syntheses this file contributes to
    """
    graph = build_unified_graph(agent_id)
    
    # Find the file node
    file_node = f"file:{filename}"
    if file_node not in graph['nodes']:
        # Try with enclave prefix
        file_node = f"file:enclave/{filename}"
    
    if file_node not in graph['nodes']:
        return f"File not found: {filename}"
    
    # Traverse
    reachable = traverse_synthesis_path(graph, file_node, max_hops=3)
    
    # Format output as dense SIF
    lines = []
    lines.append(f"@G context-{filename} {agent_id} {datetime.now().strftime('%Y-%m-%d')}")
    lines.append(f"N target File '{filename}'")
    
    # Level 4: Understanding
    if 4 in reachable:
        for item in reachable[4]:
            content = item['content'].replace("'", "\\'")[:100]
            lines.append(f"N u{item['hops']} Understanding '{content}...'")
            lines.append(f"E target has_understanding u{item['hops']}")
    
    # Level 5: Synthesis
    if 5 in reachable:
        for item in reachable[5]:
            content = item['content'].replace("'", "\\'")[:100]
            lines.append(f"N s{item['hops']} Synthesis '{content}...'")
            lines.append(f"E target contributes_to s{item['hops']}")
    
    # Level 0: Related files
    if 0 in reachable:
        related = [r for r in reachable[0] if r['id'] != file_node]
        if related:
            lines.append(f"# Related files:")
            for item in related[:5]:
                fname = item['id'].replace('file:', '')
                rel = item['path'][-1][0] if item['path'] else 'related'
                lines.append(f"E target {rel} '{fname}'")
    
    # Level 3: Thoughts
    if 3 in reachable:
        lines.append(f"# Related thoughts ({len(reachable[3])}):")
        for item in reachable[3][:3]:
            content = item['content'].replace("'", "\\'")[:80]
            lines.append(f"N t{item['hops']} Thought '{content}...'")
    
    return '\n'.join(lines)


def get_context_for_topic(agent_id: str, topic: str) -> str:
    """
    Get comprehensive context for a topic.
    
    Traverses from topic synthesis downward to find:
    - All files that contribute to this topic
    - All thoughts about this topic
    - Related topics
    """
    graph = build_unified_graph(agent_id)
    
    # Find synthesis node for this topic - check tags
    topic_lower = topic.lower().replace(' ', '-')
    synth_node = None
    
    for node_id, node in graph['nodes'].items():
        if node.get('type') == NodeType.SYNTHESIS:
            # Check tags for topic:X pattern
            tags = node.get('tags', [])
            for tag in tags:
                if tag.startswith('topic:'):
                    tag_topic = tag[6:]  # Remove 'topic:' prefix
                    if topic_lower in tag_topic.lower() or tag_topic.lower() in topic_lower:
                        synth_node = node_id
                        break
            # Also check content for @G topic
            if not synth_node:
                content = node.get('content', '').lower()
                if f'@g {topic_lower}' in content or f'{topic_lower}-synthesis' in content:
                    synth_node = node_id
            if synth_node:
                break
    
    if not synth_node:
        return f"No synthesis found for topic: {topic}"
    
    reachable = traverse_synthesis_path(graph, synth_node, max_hops=4)
    
    lines = []
    lines.append(f"@G context-{topic_lower} {agent_id} {datetime.now().strftime('%Y-%m-%d')}")
    lines.append(f"N topic Synthesis '{topic}'")
    
    # Files
    if 0 in reachable:
        lines.append(f"# Contributing files ({len(reachable[0])}):")
        for item in reachable[0]:
            fname = item['id'].replace('file:', '')
            lines.append(f"E topic grounded_in '{fname}'")
    
    # Thoughts
    if 3 in reachable:
        lines.append(f"# Related thoughts ({len(reachable[3])}):")
        for item in reachable[3][:5]:
            content = item['content'].replace('\n', ' ')[:80]
            lines.append(f"N t Thought '{content}...'")
    
    return '\n'.join(lines)


# ─────────────────────────────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────────────────────────────

def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    target = sys.argv[2]
    
    if target == '--build':
        # Build and show graph stats
        print("Building unified graph...")
        graph = build_unified_graph(agent_id)
        
        print(f"\n═══ UNIFIED GRAPH ═══")
        print(f"Total nodes: {len(graph['nodes'])}")
        print(f"Total edges: {len(graph['edges'])}")
        print()
        print("By level:")
        for level in sorted(graph['by_level'].keys()):
            count = len(graph['by_level'][level])
            level_name = {0: 'Files', 1: 'Instant', 2: 'Structure', 
                         3: 'Thoughts', 4: 'Understanding', 5: 'Synthesis'}
            print(f"  Level {level} ({level_name.get(level, '?')}): {count}")
        
        # Show edge type distribution
        edge_types = defaultdict(int)
        for src, rel, tgt in graph['edges']:
            edge_types[rel] += 1
        print()
        print("Edge types:")
        for rel, count in sorted(edge_types.items(), key=lambda x: -x[1]):
            print(f"  {rel}: {count}")
    
    elif target.endswith('.py') or target.endswith('.md'):
        # File context
        context = get_context_for_file(agent_id, target)
        print(context)
    
    else:
        # Topic context
        context = get_context_for_topic(agent_id, target)
        print(context)


if __name__ == '__main__':
    main()
