#!/usr/bin/env python3
"""
recall.py - Unified memory retrieval.

Usage:
  py recall <agent> <query>

Examples:
  py recall opus crypto.py           # exact file match
  py recall opus --theme encryption  # exact theme match  
  py recall opus "key derivation"    # semantic search → relevant graphs

The system figures out the retrieval path:
1. If query looks like a file path → exact file match
2. If --theme flag → exact theme match
3. Otherwise → semantic search, returns full graphs (not scattered nodes)
"""

import sys
import os
import hashlib
from pathlib import Path
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory
from enclave.sif_parser import TYPE_SHORTCUTS, SIFParser


# ─────────────────────────────────────────────────────────────────────────────
# Passphrase Loading
# ─────────────────────────────────────────────────────────────────────────────

def load_passphrase(agent_id: str) -> tuple[str, str]:
    """Load shared passphrase from env.
    
    Returns (enclave_dir, shared_passphrase).
    """
    agent = get_agent_or_raise(agent_id)
    
    if not agent.shared_enclave:
        raise ValueError(f"No shared_enclave configured for {agent_id}")
    enclave_dir = agent.shared_enclave
    
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
# Theme Retrieval
# ─────────────────────────────────────────────────────────────────────────────

def recall_theme(agent_id: str, theme: str):
    """Recall ALL agents' theme syntheses. Shows cross-agent visibility."""
    try:
        enclave_dir, passphrase = load_passphrase(agent_id)
        memory = SemanticMemory(enclave_dir)
        memory.unlock(passphrase)
        
        theme_slug = theme.lower().replace(' ', '-').replace('_', '-')
        all_syntheses = memory.list_by_tag('synthesis', limit=50)
        
        found = []
        for s in all_syntheses:
            tags = s.get('tags', [])
            content = s.get('content', '')
            creator = s.get('metadata', {}).get('creator', 'unknown')
            
            # Match by topic tag or graph ID
            if f'topic:{theme_slug}' in tags or f'@g {theme_slug}' in content.lower():
                found.append((creator, content))
        
        if found:
            print(f"# {theme}")
            for creator, content in found:
                print(f"\n## [by {creator}]")
                print(SIFParser.to_autocount(content))
            return
        
        # Not found
        print(f"# {theme}: NO SYNTHESIS", file=sys.stderr)
        print(f"\nStore one with:", file=sys.stderr)
        print(f"  py remember {agent_id} --theme \"{theme}\" \"@G {theme_slug} {agent_id} ...\"", file=sys.stderr)
        print(f"", file=sys.stderr)
        print(f"SIF format: N <Type> '<content>' -> <relation> <target>", file=sys.stderr)
        print(f"Types: S=Synthesis P=Purpose C=Component D=Design G=Gotcha I=Insight", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


# ─────────────────────────────────────────────────────────────────────────────
# Graph Reconstruction
# ─────────────────────────────────────────────────────────────────────────────

def compute_file_hash(filepath: Path) -> str:
    """Compute hash of file for change detection."""
    with open(filepath, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()[:12]


def reconstruct_graph(memories: list) -> dict:
    """Reconstruct understanding graph from stored memories."""
    nodes = []
    edges = []
    by_type = defaultdict(list)
    metadata = {}
    file_hashes = {}
    graph_ids = set()
    
    for mem in memories:
        meta = mem.get('metadata', {})
        graph_id = meta.get('graph_id')
        if graph_id:
            graph_ids.add(graph_id)
    
    needs_namespacing = len(graph_ids) > 1
    
    for mem in memories:
        meta = mem.get('metadata', {})
        node_type = meta.get('node_type', 'Unknown')
        node_id = meta.get('node_id', '?')
        graph_id = meta.get('graph_id', '')
        
        if needs_namespacing and graph_id and not node_id.startswith('anchor_'):
            namespaced_id = f"{graph_id}:{node_id}"
        else:
            namespaced_id = node_id
        
        content = mem.get('content', '')
        if content.startswith('['):
            content = content.split('] ', 1)[-1]
        
        nodes.append({
            'id': namespaced_id,
            'type': node_type,
            'content': content,
            'graph_id': graph_id,
            'creator': meta.get('creator', 'unknown')
        })
        by_type[node_type].append(content)
        
        for edge_info in meta.get('outgoing_edges', []):
            if isinstance(edge_info, dict):
                relation = edge_info.get('relation', '')
                target = edge_info.get('target', '')
                creator = edge_info.get('creator', 'unknown')
            else:
                relation, target = edge_info
                creator = meta.get('creator', 'unknown')
            
            if needs_namespacing and graph_id and not target.startswith('anchor_'):
                namespaced_target = f"{graph_id}:{target}"
            else:
                namespaced_target = target
            edges.append((namespaced_id, relation, namespaced_target, creator))
        
        if 'file_hashes' in meta:
            file_hashes.update(meta['file_hashes'])
        
        if node_type == 'Anchor':
            if meta.get('file_hash'):
                target = meta.get('target_path', '')
                if target:
                    file_hashes[Path(target).name] = meta['file_hash']
            metadata['timestamp'] = meta.get('timestamp')
            metadata['graph_id'] = meta.get('graph_id')
    
    metadata['file_hashes'] = file_hashes
    metadata['graph_ids'] = list(graph_ids)
    
    return {
        'nodes': nodes,
        'edges': edges,
        'by_type': dict(by_type),
        'metadata': metadata
    }


def format_as_sif(graph: dict) -> str:
    """Format graph as SIF output."""
    lines = []
    graph_id = graph['metadata'].get('graph_id', 'understanding')
    lines.append(f"@G {graph_id}")
    
    type_to_short = {v: k for k, v in TYPE_SHORTCUTS.items()}
    id_map = {}
    auto_counter = 0
    
    for node in graph['nodes']:
        if node['type'] != 'Anchor':
            auto_counter += 1
            old_id = node['id'].split(':')[-1] if ':' in node['id'] else node['id']
            id_map[old_id] = f"_{auto_counter}"
            id_map[node['id']] = f"_{auto_counter}"
            
            short_type = type_to_short.get(node['type'], node['type'])
            lines.append(f"N {short_type} '{node['content']}'")
    
    for edge in graph['edges']:
        if len(edge) == 4:
            src, rel, tgt, _ = edge
        else:
            src, rel, tgt = edge
        
        if not tgt.startswith('anchor_'):
            src_short = src.split(':')[-1] if ':' in src else src
            tgt_short = tgt.split(':')[-1] if ':' in tgt else tgt
            new_src = id_map.get(src, id_map.get(src_short, src_short))
            new_tgt = id_map.get(tgt, id_map.get(tgt_short, tgt_short))
            lines.append(f"E {new_src} {rel} {new_tgt}")
    
    return '\n'.join(lines)


# ─────────────────────────────────────────────────────────────────────────────
# File Retrieval
# ─────────────────────────────────────────────────────────────────────────────

def recall_file(mem: SemanticMemory, agent_id: str, target_path: str, filename: str):
    """Recall understanding for a single file."""
    results = mem.list_by_tag(filename, limit=100)
    
    if not results:
        results = mem.list_by_metadata('target_path', filename, limit=100)
    
    if not results:
        results = mem.recall_similar(f"[Component] {filename}", top_k=100, threshold=0.1)
    
    individual_nodes = []
    current_agent_has_understanding = False
    
    for mem_entry in results:
        meta = mem_entry.get('metadata', {})
        stored_path = meta.get('target_path', '')
        creator = meta.get('creator', '')
        
        stored_files = [p.strip() for p in stored_path.split(',')]
        stored_names = [Path(p).name for p in stored_files]
        if filename in stored_names or filename in stored_path:
            if creator == agent_id:
                current_agent_has_understanding = True
            if creator != 'synthesis':
                individual_nodes.append(mem_entry)
    
    # Blind until stored
    if not current_agent_has_understanding and individual_nodes:
        other_creators = set(m.get('metadata', {}).get('creator') for m in individual_nodes)
        other_creators.discard(agent_id)
        if other_creators:
            print(f"# {filename}: BLIND (others: {', '.join(sorted(other_creators))})")
            return
    
    relevant = [n for n in individual_nodes if n.get('metadata', {}).get('creator') == agent_id]
    
    if not relevant:
        if individual_nodes:
            print(f"# {filename}: no understanding by {agent_id}")
        else:
            print(f"# {filename}: no understanding stored")
        return
    
    graph = reconstruct_graph(relevant)
    print(f"# {filename}")
    print(format_as_sif(graph))


# ─────────────────────────────────────────────────────────────────────────────
# Semantic Retrieval
# ─────────────────────────────────────────────────────────────────────────────

def recall_semantic(mem: SemanticMemory, agent_id: str, query: str):
    """Semantic search returning full graphs."""
    results = mem.recall_similar(query, top_k=100, threshold=0.2)
    
    if not results:
        print(f"# No memories match: {query}")
        return
    
    # Group by graph_id - include ALL creators for shared topic visibility
    graphs = defaultdict(list)
    graph_creators = {}  # Track creator per graph for labeling
    for r in results:
        meta = r.get('metadata', {})
        graph_id = meta.get('graph_id', 'unknown')
        creator = meta.get('creator', 'unknown')
        
        graphs[graph_id].append(r)
        graph_creators[graph_id] = creator
    
    if not graphs:
        print(f"# No memories match: {query}")
        return
    
    # Sort by relevance
    graph_scores = {g: sum(n.get('similarity', 0) for n in nodes) for g, nodes in graphs.items()}
    sorted_graphs = sorted(graph_scores.keys(), key=lambda g: graph_scores[g], reverse=True)
    
    print(f"# Semantic recall: {query}")
    print(f"# Found {len(sorted_graphs)} relevant graphs")
    print()
    
    for graph_id in sorted_graphs[:3]:
        nodes = graphs[graph_id]
        score = graph_scores[graph_id]
        creator = graph_creators.get(graph_id, 'unknown')
        
        graph = reconstruct_graph(nodes)
        
        target_path = None
        for n in nodes:
            tp = n.get('metadata', {}).get('target_path')
            if tp:
                target_path = tp
                break
        
        print(f"## {graph_id} [by {creator}] (relevance: {score:.2f})")
        if target_path:
            print(f"# file: {target_path}")
        print(format_as_sif(graph))
        print()


# ─────────────────────────────────────────────────────────────────────────────
# Query Detection
# ─────────────────────────────────────────────────────────────────────────────

def is_file_query(query: str) -> bool:
    """Detect if query looks like a file path."""
    extensions = ['.py', '.md', '.txt', '.json', '.sif', '.yaml', '.yml', '.js', '.ts']
    if '.' in query and any(query.endswith(ext) for ext in extensions):
        return True
    if '/' in query or '\\' in query:
        return True
    if '*' in query:
        return True
    return False


# ─────────────────────────────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────────────────────────────

def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    
    # Theme mode
    if '--theme' in sys.argv:
        theme_idx = sys.argv.index('--theme')
        if len(sys.argv) < theme_idx + 2:
            print("Usage: py recall <agent> --theme <theme>", file=sys.stderr)
            sys.exit(1)
        theme = sys.argv[theme_idx + 1]
        recall_theme(agent_id, theme)
        return
    
    query = ' '.join(sys.argv[2:])
    
    try:
        enclave_dir, passphrase = load_passphrase(agent_id)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    
    mem = SemanticMemory(enclave_dir)
    mem.unlock(passphrase)
    
    if is_file_query(query):
        # File retrieval
        if '*' in query:
            target_paths = list(Path('.').glob(query))
            if not target_paths:
                print(f"No files match: {query}", file=sys.stderr)
                sys.exit(1)
            for target_path in target_paths:
                recall_file(mem, agent_id, str(target_path), target_path.name)
        else:
            target_path = Path(query)
            recall_file(mem, agent_id, str(target_path), target_path.name)
    else:
        # Semantic retrieval
        recall_semantic(mem, agent_id, query)


if __name__ == "__main__":
    main()
