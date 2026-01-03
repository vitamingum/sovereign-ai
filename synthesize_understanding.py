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


def load_understanding_graphs(mem: SemanticMemory, filepath: str) -> Dict[str, dict]:
    """Load all agents' understanding graphs for a file.
    
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
    
    # Build output SIF
    filename = os.path.basename(filepath)
    timestamp = datetime.now(timezone.utc).strftime('%Y-%m-%d')
    agents_str = '+'.join(sorted(graphs.keys()))
    
    sif_lines = [f"@G {filename.replace('.', '-')}-unified-synthesis {agents_str} {timestamp}"]
    
    # Group nodes by match type for clearer output
    for match_type in ['same', 'related', 'unique']:
        type_nodes = [n for n in unified_nodes if n['match_type'] == match_type]
        if type_nodes:
            if match_type == 'same':
                sif_lines.append(f"\n# MERGED ({len(type_nodes)} nodes - both agents agree)")
            elif match_type == 'related':
                sif_lines.append(f"\n# RELATED ({len(type_nodes)} nodes - connected insights)")
            else:
                sif_lines.append(f"\n# UNIQUE ({len(type_nodes)} nodes - single agent insight)")
            
            for node in type_nodes:
                creators = '+'.join(node['creators'])
                sim_note = f" sim={node['similarity']:.2f}" if node['similarity'] else ""
                sif_lines.append(f"N {node['id']} {node['type']} '{node['content']}' creator={creators}{sim_note}")
    
    # Add edges
    sif_lines.append(f"\n# RELATIONSHIPS ({len(unified_edges)} edges)")
    seen_edges = set()
    for edge in unified_edges:
        edge_key = (edge['source'], edge['target'], edge['relation'])
        if edge_key in seen_edges:
            continue
        seen_edges.add(edge_key)
        sif_lines.append(f"E {edge['source']} {edge['relation']} {edge['target']}")
    
    return '\n'.join(sif_lines)


def compress_synthesis(verbose_sif: str, filepath: str, agents: List[str], llm: LocalLLM) -> str:
    """Use LLM to compress verbose synthesis into dense SIF.
    
    Target: ~12-15 nodes max, one concept per node, preserve attribution.
    """
    filename = os.path.basename(filepath)
    agents_str = '+'.join(sorted(agents))
    timestamp = datetime.now(timezone.utc).strftime('%Y-%m-%d')
    
    prompt = f"""Compress this verbose understanding into dense SIF format.

VERBOSE INPUT:
{verbose_sif}

RULES:
1. Maximum 15 nodes total
2. Merge redundant concepts into single nodes
3. Keep attribution: creator=both if both agents agree, else creator=<agent>
4. Use TYPE_SHORTCUTS: C=Component, P=Purpose, D=Design, G=Gotcha, A=Assumption, F=Failure_Mode, Rule=Rule
5. One insight per node - be concise
6. Keep the most important edges (max 12)

OUTPUT FORMAT (exactly this, no explanation):
@G {filename.replace('.', '-')}-synthesis {agents_str} {timestamp}
N c1 C 'component description' creator=both
N p1 P 'purpose' creator=<agent>
...
E c1 implements p1
...

Generate the compressed SIF now:"""

    try:
        response = llm.generate(prompt)
        
        # Extract just the SIF part (starts with @G)
        lines = response.strip().split('\n')
        sif_lines = []
        in_sif = False
        for line in lines:
            if line.strip().startswith('@G'):
                in_sif = True
            if in_sif:
                sif_lines.append(line)
        
        if sif_lines:
            return '\n'.join(sif_lines)
        else:
            # Fallback - return as-is if parsing failed
            return response.strip()
    except Exception as e:
        print(f"  LLM compression failed: {e}")
        return verbose_sif


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
    
    print(f"\n🔬 Synthesizing {len(graphs)} perspectives...")
    llm = LocalLLM()
    
    verbose_synthesis = synthesize_graphs(graphs, filepath, llm)
    
    print(f"\n═══ VERBOSE SYNTHESIS ({verbose_synthesis.count(chr(10))} lines) ═══")
    # Count nodes
    node_count = verbose_synthesis.count('\nN ')
    print(f"  {node_count} nodes before compression")
    
    print(f"\n🗜️  Compressing with LLM...")
    dense_synthesis = compress_synthesis(verbose_synthesis, filepath, list(graphs.keys()), llm)
    
    print(f"\n═══ DENSE SYNTHESIS ═══")
    print(dense_synthesis)
    
    # Count compressed nodes
    dense_node_count = dense_synthesis.count('\nN ') + (1 if dense_synthesis.startswith('N ') else 0)
    print(f"\n  Compressed: {node_count} → {dense_node_count} nodes")


if __name__ == '__main__':
    main()
