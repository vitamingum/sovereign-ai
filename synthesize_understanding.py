# hash: 0000000000000000
"""
Synthesize multi-agent understanding into unified knowledge graph.

Usage:
    python synthesize_understanding.py <agent> <file>
    
Example:
    python synthesize_understanding.py opus judge.py
    
Takes all agents' understanding of a file and produces:
1. Merged nodes (same insight from multiple agents)
2. Unique nodes (one agent's exclusive insight)
3. Cross-agent agreement edges
4. Unified synthesis stored with topic:synthesis tag
"""

import sys
import os
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Tuple, Set
import numpy as np

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent))

from wake import load_passphrase
from enclave.semantic_memory import SemanticMemory
from enclave.sif_parser import SIFParser, SIFKnowledgeGraph
from enclave.llm import LocalLLM


def parse_sif(content: str) -> SIFKnowledgeGraph:
    """Parse SIF content into a knowledge graph."""
    parser = SIFParser()
    return parser.parse(content)


def get_embedding(text: str, model=None) -> List[float]:
    """Get embedding for text using sentence transformer."""
    if model is None:
        from sentence_transformers import SentenceTransformer
        model = SentenceTransformer('nomic-ai/nomic-embed-text-v1.5', trust_remote_code=True)
    embedding = model.encode(text, normalize_embeddings=True)
    return embedding.tolist()


SIMILARITY_THRESHOLD_HIGH = 0.85  # Definitely same insight
SIMILARITY_THRESHOLD_LOW = 0.60   # Ask LLM to decide


def cosine_similarity(a: List[float], b: List[float]) -> float:
    """Compute cosine similarity between two vectors."""
    a = np.array(a)
    b = np.array(b)
    return float(np.dot(a, b) / (np.linalg.norm(a) * np.linalg.norm(b)))


def load_understanding_graphs(mem: SemanticMemory, filepath: str, exclude_synthesis: bool = True) -> Dict[str, dict]:
    """Load all agents' understanding graphs for a file.
    
    Args:
        mem: SemanticMemory instance
        filepath: File to load understanding for
        exclude_synthesis: If True, skip nodes with creator=synthesis (default True)
    
    Returns dict of agent -> {nodes: [...], edges: [...]}
    """
    filename = os.path.basename(filepath)
    
    # Get all nodes tagged with this file using list_by_tag (more complete)
    results = mem.list_by_tag(filename, limit=100)
    
    # Group by creator/agent
    graphs = {}  # agent -> {nodes: [], edges: []}
    
    for result in results:
        tags = result.get('tags', [])
        metadata = result.get('metadata', {})
        content = result.get('content', '')
        
        # Get creator from metadata or parse from graph_id tag
        creator = metadata.get('creator')
        if not creator:
            for tag in tags:
                if ':' in tag and '-understanding' in tag:
                    creator = tag.split(':')[0]
                    break
        
        # Default to opus if no creator found (legacy data)
        if not creator:
            creator = 'opus'
        
        # Skip synthesis nodes when building input for new synthesis
        if exclude_synthesis and creator == 'synthesis':
            continue
        
        if creator not in graphs:
            graphs[creator] = {'nodes': [], 'edges': [], 'raw_results': []}
        
        # Extract node info
        node_type = metadata.get('node_type', tags[0] if tags else 'Unknown')
        node_id = metadata.get('node_id', f'n{len(graphs[creator]["nodes"])}')
        
        # Parse content like "[Component] judge.py - Cognitive Gatekeeper"
        if content.startswith('['):
            bracket_end = content.find(']')
            if bracket_end > 0:
                node_type_from_content = content[1:bracket_end]
                node_content = content[bracket_end + 1:].strip()
                if not metadata.get('node_type'):
                    node_type = node_type_from_content
            else:
                node_content = content
        else:
            node_content = content
        
        graphs[creator]['nodes'].append({
            'id': node_id,
            'type': node_type,
            'content': node_content,
            'creator': creator
        })
        
        # Extract edges from metadata
        for rel, target in metadata.get('outgoing_edges', []):
            graphs[creator]['edges'].append({
                'source': node_id,
                'relation': rel,
                'target': target
            })
        
        graphs[creator]['raw_results'].append(result)
    
    for agent, data in graphs.items():
        print(f"  Loaded {agent}'s understanding: {len(data['nodes'])} nodes, {len(data['edges'])} edges")
    
    return graphs


# Global model cache
_embedding_model = None

def get_node_embedding(node, cache: Dict[str, List[float]]) -> List[float]:
    """Get or compute embedding for a node's content."""
    global _embedding_model
    content = node.content if hasattr(node, 'content') else str(node)
    if content not in cache:
        if _embedding_model is None:
            from sentence_transformers import SentenceTransformer
            _embedding_model = SentenceTransformer('nomic-ai/nomic-embed-text-v1.5', trust_remote_code=True)
        embedding = _embedding_model.encode(content, normalize_embeddings=True)
        cache[content] = embedding.tolist()
    return cache[content]


def find_similar_nodes(
    nodes_a: List, 
    nodes_b: List, 
    embedding_cache: Dict[str, List[float]],
    llm: LocalLLM
) -> List[Tuple[any, any, float, str]]:
    """Find semantically similar nodes between two sets.
    
    Returns: List of (node_a, node_b, similarity, verdict)
    where verdict is 'same', 'related', or 'different'
    """
    matches = []
    
    for na in nodes_a:
        for nb in nodes_b:
            # Only compare same types
            na_type = na.type if hasattr(na, 'type') else 'Unknown'
            nb_type = nb.type if hasattr(nb, 'type') else 'Unknown'
            if na_type != nb_type:
                continue
            
            # Get embeddings and compute similarity
            emb_a = get_node_embedding(na, embedding_cache)
            emb_b = get_node_embedding(nb, embedding_cache)
            sim = cosine_similarity(emb_a, emb_b)
            
            if sim >= SIMILARITY_THRESHOLD_HIGH:
                matches.append((na, nb, sim, 'same'))
            elif sim >= SIMILARITY_THRESHOLD_LOW:
                # Ask LLM to decide
                verdict = ask_llm_similarity(na.content, nb.content, llm)
                if verdict in ('same', 'related'):
                    matches.append((na, nb, sim, verdict))
    
    return matches


def ask_llm_similarity(content_a: str, content_b: str, llm: LocalLLM) -> str:
    """Ask LLM whether two nodes express the same insight."""
    prompt = f"""Compare these two statements about the same codebase:

A: {content_a}
B: {content_b}

Are they:
- "same": expressing the same insight (just worded differently)
- "related": connected but distinct insights  
- "different": unrelated insights

Respond with just the word: same, related, or different"""

    try:
        response = llm.generate(prompt, max_tokens=10)
        response = response.strip().lower()
        if 'same' in response:
            return 'same'
        elif 'related' in response:
            return 'related'
        else:
            return 'different'
    except Exception:
        return 'different'  # Conservative fallback


def find_similar_nodes_dict(
    nodes_a: List[dict], 
    nodes_b: List[dict], 
    embedding_cache: Dict[str, List[float]],
    llm: LocalLLM
) -> List[Tuple[dict, dict, float, str]]:
    """Find semantically similar nodes between two sets (dict version).
    
    Returns: List of (node_a, node_b, similarity, verdict)
    """
    matches = []
    
    for na in nodes_a:
        for nb in nodes_b:
            # Only compare same types
            na_type = na.get('type', 'Unknown')
            nb_type = nb.get('type', 'Unknown')
            if na_type != nb_type:
                continue
            
            # Get embeddings and compute similarity
            emb_a = get_node_embedding_dict(na, embedding_cache)
            emb_b = get_node_embedding_dict(nb, embedding_cache)
            sim = cosine_similarity(emb_a, emb_b)
            
            if sim >= SIMILARITY_THRESHOLD_HIGH:
                matches.append((na, nb, sim, 'same'))
            elif sim >= SIMILARITY_THRESHOLD_LOW:
                # Ask LLM to decide
                verdict = ask_llm_similarity(na['content'], nb['content'], llm)
                if verdict in ('same', 'related'):
                    matches.append((na, nb, sim, verdict))
    
    return matches


def get_node_embedding_dict(node: dict, cache: Dict[str, List[float]]) -> List[float]:
    """Get or compute embedding for a node dict's content."""
    global _embedding_model
    content = node.get('content', str(node))
    if content not in cache:
        if _embedding_model is None:
            from sentence_transformers import SentenceTransformer
            _embedding_model = SentenceTransformer('nomic-ai/nomic-embed-text-v1.5', trust_remote_code=True)
        embedding = _embedding_model.encode(content, normalize_embeddings=True)
        cache[content] = embedding.tolist()
    return cache[content]


def synthesize_graphs(
    graphs: Dict[str, dict],
    filepath: str,
    llm: LocalLLM
) -> str:
    """Synthesize multiple understanding graphs into one unified graph.
    
    graphs: Dict of agent -> {nodes: [...], edges: [...]}
    Returns: SIF string
    """
    
    if len(graphs) < 2:
        print("  Need at least 2 agents' understanding to synthesize")
        return None
    
    embedding_cache: Dict[str, List[float]] = {}
    agents = list(graphs.keys())
    
    # Collect all nodes by type
    all_nodes_by_type: Dict[str, Dict[str, List]] = {}  # type -> agent -> nodes
    for agent, graph_data in graphs.items():
        for node in graph_data['nodes']:
            ntype = node.get('type', 'Unknown')
            if ntype.lower() == 'anchor':  # Skip anchors
                continue
            if ntype not in all_nodes_by_type:
                all_nodes_by_type[ntype] = {}
            if agent not in all_nodes_by_type[ntype]:
                all_nodes_by_type[ntype][agent] = []
            all_nodes_by_type[ntype][agent].append(node)
    
    # Find matches between agents
    matches = []
    for ntype, agents_nodes in all_nodes_by_type.items():
        agent_list = list(agents_nodes.keys())
        for i in range(len(agent_list)):
            for j in range(i + 1, len(agent_list)):
                a1, a2 = agent_list[i], agent_list[j]
                type_matches = find_similar_nodes_dict(
                    agents_nodes[a1], 
                    agents_nodes[a2],
                    embedding_cache,
                    llm
                )
                for na, nb, sim, verdict in type_matches:
                    matches.append({
                        'agent_a': a1,
                        'agent_b': a2,
                        'node_a': na,
                        'node_b': nb,
                        'similarity': sim,
                        'verdict': verdict
                    })
    
    # Build unified graph
    unified_nodes = []
    unified_edges = []
    merged_ids: Set[str] = set()
    node_id_counter = 1
    
    # Track which nodes have been merged
    node_to_unified: Dict[str, str] = {}  # "agent:node_id" -> unified_id
    
    # Process matches - create merged nodes
    print(f"\n  Found {len(matches)} cross-agent matches:")
    for match in matches:
        na, nb = match['node_a'], match['node_b']
        verdict = match['verdict']
        
        # Use the longer/more specific content
        content_a = na.get('content', str(na))
        content_b = nb.get('content', str(nb))
        merged_content = content_a if len(content_a) >= len(content_b) else content_b
        
        na_id = na.get('id', str(na))
        nb_id = nb.get('id', str(nb))
        
        key_a = f"{match['agent_a']}:{na_id}"
        key_b = f"{match['agent_b']}:{nb_id}"
        
        if key_a in merged_ids or key_b in merged_ids:
            continue
            
        merged_ids.add(key_a)
        merged_ids.add(key_b)
        
        unified_id = f"m{node_id_counter}"
        node_id_counter += 1
        
        node_to_unified[key_a] = unified_id
        node_to_unified[key_b] = unified_id
        
        ntype = na.get('type', 'Component')
        
        unified_nodes.append({
            'id': unified_id,
            'type': ntype,
            'content': merged_content,
            'creators': [match['agent_a'], match['agent_b']],
            'match_type': verdict,
            'similarity': match['similarity']
        })
        
        print(f"    [{verdict}] {ntype}: {content_a[:40]}... ≈ {content_b[:40]}...")
    
    # Add unmerged nodes (unique insights)
    print(f"\n  Unique insights:")
    for agent, graph_data in graphs.items():
        for node in graph_data['nodes']:
            node_id = node.get('id', str(node))
            key = f"{agent}:{node_id}"
            
            if key in merged_ids:
                continue
            
            # Skip anchor nodes
            ntype = node.get('type', 'Unknown')
            if ntype.lower() == 'anchor':
                continue
                
            unified_id = f"u{node_id_counter}"
            node_id_counter += 1
            
            node_to_unified[key] = unified_id
            
            content = node.get('content', str(node))
            
            unified_nodes.append({
                'id': unified_id,
                'type': ntype,
                'content': content,
                'creators': [agent],
                'match_type': 'unique',
                'similarity': None
            })
            
            print(f"    [{agent}] {ntype}: {content[:60]}...")
    
    # Collect edges from all graphs
    for agent, graph_data in graphs.items():
        for edge in graph_data['edges']:
            src_id = edge.get('source', edge[0] if isinstance(edge, tuple) else None)
            tgt_id = edge.get('target', edge[1] if isinstance(edge, tuple) else None)
            rel = edge.get('relation', 'related')
            
            src_key = f"{agent}:{src_id}"
            tgt_key = f"{agent}:{tgt_id}"
            
            unified_src = node_to_unified.get(src_key)
            unified_tgt = node_to_unified.get(tgt_key)
            
            if unified_src and unified_tgt:
                unified_edges.append({
                    'source': unified_src,
                    'target': unified_tgt,
                    'relation': rel,
                    'creator': agent
                })
    
    # Add cross-agent agreement edges
    print(f"\n  Cross-agent agreement edges:")
    for match in matches:
        if match['verdict'] == 'same':
            na_id = match['node_a'].get('id', str(match['node_a']))
            nb_id = match['node_b'].get('id', str(match['node_b']))
            
            key_a = f"{match['agent_a']}:{na_id}"
            key_b = f"{match['agent_b']}:{nb_id}"
            
            # Add agreement metadata (not a graph edge, but recorded)
            print(f"    {match['agent_a']} agrees_with {match['agent_b']} on: {match['node_a'].get('content', '')[:40]}...")
    
    # Build DENSE output SIF - no comments, no verbose IDs
    filename = os.path.basename(filepath)
    timestamp = datetime.now(timezone.utc).strftime('%Y-%m-%d')
    agents_str = '+'.join(sorted(graphs.keys()))
    
    sif_lines = [f"@G {filename.replace('.', '-')}-synthesis {agents_str} {timestamp}"]
    
    # Assign sequential dense IDs by type
    type_counters = {}
    TYPE_PREFIXES = {
        'Component': 'c', 'Purpose': 'p', 'Design_Decision': 'd',
        'Gotcha': 'g', 'Assumption': 'a', 'Failure_Mode': 'f',
        'Rule': 'r', 'Insight': 'i', 'Anchor': 'x'
    }
    
    # Map old IDs to new dense IDs
    id_remap = {}
    
    for node in unified_nodes:
        node_type = node['type']
        prefix = TYPE_PREFIXES.get(node_type, 'n')
        type_counters[prefix] = type_counters.get(prefix, 0) + 1
        new_id = f"{prefix}{type_counters[prefix]}"
        id_remap[node['id']] = new_id
        
        # Dense creator: 'both' if multiple, else single agent
        if len(node['creators']) > 1:
            creator = 'both'
        else:
            creator = node['creators'][0]
        
        sif_lines.append(f"N {new_id} {node_type} '{node['content']}' creator={creator}")
    
    # Add edges with remapped IDs
    seen_edges = set()
    for edge in unified_edges:
        new_src = id_remap.get(edge['source'], edge['source'])
        new_tgt = id_remap.get(edge['target'], edge['target'])
        edge_key = (new_src, new_tgt, edge['relation'])
        if edge_key in seen_edges:
            continue
        seen_edges.add(edge_key)
        sif_lines.append(f"E {new_src} {edge['relation']} {new_tgt}")
    
    return '\n'.join(sif_lines)


def main():
    if len(sys.argv) < 3:
        print("Usage: python synthesize_understanding.py <agent> <file>")
        print("Example: python synthesize_understanding.py opus judge.py")
        sys.exit(1)
    
    agent = sys.argv[1]
    filepath = sys.argv[2]
    
    print(f"═══ SYNTHESIZE UNDERSTANDING: {filepath} ═══")
    
    # Load passphrase and memory
    shared_dir, private_dir, shared_pass, private_pass = load_passphrase(agent)
    mem = SemanticMemory(shared_dir)
    mem.unlock(shared_pass)
    
    print(f"\n📥 Loading understanding graphs...")
    graphs = load_understanding_graphs(mem, filepath)
    
    if not graphs:
        print(f"  No understanding found for {filepath}")
        sys.exit(1)
    
    if len(graphs) < 2:
        print(f"  Only {len(graphs)} agent(s) - need 2+ for synthesis")
        sys.exit(1)
    
    print(f"\n🔬 Synthesizing {len(graphs)} perspectives...")
    llm = LocalLLM()
    
    synthesis = synthesize_graphs(graphs, filepath, llm)
    
    print(f"\n═══ SYNTHESIS ═══")
    print(synthesis)
    
    # Count nodes in synthesis
    node_count = synthesis.count('\nN ') + (1 if synthesis.startswith('N ') else 0)
    merged = synthesis.count('creator=gemini+opus') + synthesis.count('creator=opus+gemini')
    unique = node_count - merged
    print(f"\n  Result: {node_count} nodes ({merged} merged, {unique} unique)")
    
    # Store the synthesis
    stored = store_synthesis(mem, synthesis, filepath)
    print(f"\n✓ Stored synthesis ({stored} nodes)")


def store_synthesis(mem: SemanticMemory, synthesis_sif: str, filepath: str) -> int:
    """Store synthesis to semantic memory with creator=synthesis.
    
    Replaces any existing synthesis for this file.
    """
    from enclave.sif_parser import SIFParser
    
    filename = os.path.basename(filepath)
    timestamp = datetime.now(timezone.utc).isoformat()
    
    # Delete existing synthesis for this file
    existing = mem.list_by_tag(filename, limit=200)
    ids_to_delete = set()
    for node in existing:
        metadata = node.get('metadata', {})
        if metadata.get('creator') == 'synthesis':
            ids_to_delete.add(node['id'])
    
    if ids_to_delete:
        deleted = mem.delete_by_ids(ids_to_delete)
        print(f"  [REPLACED] Deleted {deleted} old synthesis nodes")
    
    # Parse the synthesis SIF
    parser = SIFParser()
    graph = parser.parse(synthesis_sif)
    
    # Store each node
    stored_count = 0
    for node in graph.nodes:
        searchable = f"[{node.type}] {node.content}"
        
        # Extract creators from node content (e.g., "creator=gemini+opus")
        sources = []
        if hasattr(node, 'creator') and node.creator:
            sources = node.creator.split('+')
        
        outgoing = [e for e in graph.edges if e.source == node.id]
        incoming = [e for e in graph.edges if e.target == node.id]
        
        metadata = {
            "graph_id": graph.id,
            "node_id": node.id,
            "node_type": node.type,
            "target_path": filepath,
            "timestamp": timestamp,
            "creator": "synthesis",
            "sources": sources,  # Which agents contributed
            "outgoing_edges": [(e.relation, e.target) for e in outgoing],
            "incoming_edges": [(e.source, e.relation) for e in incoming],
        }
        
        mem.remember(
            thought=searchable,
            tags=[node.type.lower(), graph.id, filename, "synthesis"],
            metadata=metadata
        )
        stored_count += 1
    
    return stored_count


def maybe_synthesize(mem: SemanticMemory, filepath: str, current_agent: str) -> bool:
    """Check if synthesis should run and do it.
    
    Returns True if synthesis was created/updated.
    Called after remember.py stores understanding.
    """
    graphs = load_understanding_graphs(mem, filepath)
    
    # Filter out synthesis itself
    graphs = {k: v for k, v in graphs.items() if k != 'synthesis'}
    
    if len(graphs) < 2:
        return False  # Need 2+ perspectives
    
    print(f"\n🔬 Auto-synthesizing {len(graphs)} perspectives on {filepath}...")
    llm = LocalLLM()
    
    synthesis = synthesize_graphs(graphs, filepath, llm)
    stored = store_synthesis(mem, synthesis, filepath)
    
    print(f"  ✓ Synthesis stored ({stored} nodes from {'+'.join(graphs.keys())})")
    return True


if __name__ == '__main__':
    main()
