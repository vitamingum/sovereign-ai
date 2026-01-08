#!/usr/bin/env python3
"""
recall.py - Unified memory retrieval.

Usage:
  py recall <agent> <query>

Examples:
  py recall opus crypto.py           # exact file match
  py recall opus --theme encryption  # exact theme match  
  py recall opus "key derivation"    # semantic search (graphs + journal)
  py recall opus --literal "exact phrase"  # O(N) literal string search

The system figures out the retrieval path:
1. If query looks like a file path → exact file match
2. If --theme flag → exact theme match
3. If --literal flag → brute-force string search (O(N), no embeddings)
4. Otherwise → semantic search across shared graphs AND private journal
"""

import sys
import os
import io
import hashlib
from pathlib import Path
from collections import defaultdict

# Fix Windows console encoding for Unicode output
if sys.stdout.encoding != 'utf-8':
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
if sys.stderr.encoding != 'utf-8':
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8', errors='replace')

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import json

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


def load_private_passphrase(agent_id: str) -> tuple[str, str]:
    """Load agent's private passphrase for journal access.
    
    Returns (private_enclave_dir, private_passphrase).
    """
    agent = get_agent_or_raise(agent_id)
    enclave_dir = agent.private_enclave
    
    passphrase = os.environ.get(f'{agent.env_prefix}_KEY')
    
    if not passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith(f'{agent.env_prefix}_KEY='):
                        passphrase = line.split('=', 1)[1]
    
    if not passphrase:
        raise ValueError(f"No private passphrase. Set {agent.env_prefix}_KEY in .env")
    
    return enclave_dir, passphrase


# ─────────────────────────────────────────────────────────────────────────────
# Theme Retrieval
# ─────────────────────────────────────────────────────────────────────────────

def fuzzy_match_themes(query: str, candidates: list[dict], max_results: int = 3) -> list[dict]:
    """
    Find most relevant themes using single LLM call.
    candidates: list of {'id': str, 'topic': str, 'graph_id': str, ...}
    Returns top matches sorted by relevance.
    """
    # Fast path: exact/substring matches
    exact = []
    partial = []  # Word overlap but not substring
    fuzzy_candidates = []
    
    query_words = set(query.replace('-', ' ').split())
    
    for c in candidates:
        topic = c.get('topic') or ''
        graph_id = c.get('graph_id') or ''
        
        # Check substring match (handle empty strings)
        topic_match = topic and (query in topic or topic in query)
        graph_match = graph_id and (query in graph_id or graph_id in query)
        
        if topic_match or graph_match:
            c['match_type'] = 'exact'
            exact.append(c)
        else:
            # Check word overlap (e.g., "pure-sif" matches "forge-pure-sif")
            topic_words = set(topic.replace('-', ' ').split()) if topic else set()
            graph_words = set(graph_id.replace('-', ' ').split()) if graph_id else set()
            all_words = topic_words | graph_words
            
            overlap = query_words & all_words
            if overlap:
                c['match_type'] = 'partial'
                c['overlap'] = len(overlap)
                partial.append(c)
            else:
                fuzzy_candidates.append(c)
    
    # Sort partial by overlap count (most overlap first)
    partial.sort(key=lambda x: -x.get('overlap', 0))
    
    # Combine: exact first, then partial, then fuzzy
    results = exact + partial
    
    # If we have enough, skip LLM
    if len(results) >= max_results:
        return results[:max_results]
    
    # Need fuzzy matches - one LLM call for all candidates
    if fuzzy_candidates and len(results) < max_results:
        needed = max_results - len(results)
        try:
            from enclave.llm import LocalLLM
            llm = LocalLLM(model="qwen2.5-coder:7b")
            
            # Build candidate list for prompt
            candidate_list = "\n".join([
                f"  {i+1}. {c.get('topic') or c.get('graph_id', 'unknown')}"
                for i, c in enumerate(fuzzy_candidates[:20])  # Cap at 20
            ])
            
            prompt = f"""Which of these topics are most related to "{query}"?
{candidate_list}

Return ONLY the numbers of the top {needed} most related (comma-separated), or "none" if none are related."""
            
            response = llm.generate(prompt).strip().lower()
            
            if response != 'none':
                # Parse numbers from response
                import re
                numbers = re.findall(r'\d+', response)
                for num_str in numbers[:needed]:
                    idx = int(num_str) - 1
                    if 0 <= idx < len(fuzzy_candidates):
                        fuzzy_candidates[idx]['match_type'] = 'fuzzy'
                        results.append(fuzzy_candidates[idx])
        except Exception:
            pass  # Skip fuzzy if LLM fails
    
    return results


def recall_theme(agent_id: str, theme: str):
    """Recall ALL agents' theme syntheses. Shows cross-agent visibility. Max 1 per agent."""
    from datetime import datetime
    try:
        enclave_dir, passphrase = load_passphrase(agent_id)
        memory = SemanticMemory(enclave_dir)
        memory.unlock(passphrase)
        
        theme_slug = theme.lower().replace(' ', '-').replace('_', '-')
        
        # Look for themes stored with either 'synthesis' or 'theme' tag
        all_syntheses = []
        for tag in ['synthesis', 'theme']:
            entries = memory.list_by_tag(tag, limit=100)
            for e in entries:
                if e not in all_syntheses:
                    all_syntheses.append(e)
        
        # Build candidate list with metadata
        candidates = []
        exact_matches = []  # Track exact matches separately
        
        for s in all_syntheses:
            tags = s.get('tags', [])
            content = s.get('content', '')
            creator = s.get('metadata', {}).get('creator', 'unknown')
            timestamp = s.get('timestamp', '')
            
            # Extract topic from tags
            topic = None
            for tag in tags:
                if tag.startswith('topic:'):
                    topic = tag[6:]
                    break
            
            # Extract graph ID from @G line
            graph_id = None
            content_lower = content.lower()
            if '@g ' in content_lower:
                for line in content_lower.split('\n'):
                    if line.strip().startswith('@g '):
                        parts = line.strip().split()
                        if len(parts) > 1:
                            graph_id = parts[1]
                            break
            
            entry = {
                'topic': topic,
                'graph_id': graph_id,
                'creator': creator,
                'content': content,
                'timestamp': timestamp,
                'match_type': 'exact'
            }
            
            # Check for exact topic match FIRST
            if topic and topic == theme_slug:
                exact_matches.append(entry)
            else:
                candidates.append(entry)
        
        # ONLY use fuzzy matching if NO exact matches exist
        if exact_matches:
            found = exact_matches
        else:
            # No exact matches - try fuzzy
            found = fuzzy_match_themes(theme_slug, candidates, max_results=50)
        
        if found:
            # Group by agent, keep only newest per agent
            by_agent = {}
            for entry in found:
                creator = entry['creator']
                if creator not in by_agent or entry['timestamp'] > by_agent[creator]['timestamp']:
                    by_agent[creator] = entry
            
            # Convert back to list and sort by timestamp (oldest first)
            found = list(by_agent.values())
            found.sort(key=lambda x: x['timestamp'])
            
            # Find newest timestamp for staleness detection
            newest_ts = found[-1]['timestamp'] if found else ''
            
            # Show actual theme ID found, not search term
            display_id = found[-1].get('topic') or found[-1].get('graph_id') or theme
            print(f"# {display_id}")
            
            for entry in found:
                creator = entry['creator']
                content = entry['content']
                ts = entry['timestamp']
                match_type = entry.get('match_type', '')
                actual_id = entry.get('topic') or entry.get('graph_id') or '?'
                
                # Format timestamp for display
                ts_display = ts[:19].replace('T', ' ') if ts else 'unknown'
                
                # Mark as stale if not the newest
                stale_marker = " ⚠️ STALE" if ts != newest_ts else ""
                fuzzy_marker = " 🔍" if match_type == 'fuzzy' else ""
                
                print(f"\n## [{actual_id}] by {creator} @ {ts_display}{stale_marker}{fuzzy_marker}")
                
                # Detect format and output appropriately
                if content.strip().startswith('@F '):
                    # Flow format - output directly (no SIF transformation)
                    print(content)
                else:
                    # SIF format - use autocount parser
                    print(SIFParser.to_autocount(content))
            return
        
        # Not found
        print(f"# {theme}: NO SYNTHESIS", file=sys.stderr)
        print(f"\nStore one with (Flow preferred):", file=sys.stderr)
        print(f"  py remember {agent_id} --theme \"{theme}\" \"@{theme_slug}.flow\"", file=sys.stderr)
        print(f"", file=sys.stderr)
        print(f"Flow format:", file=sys.stderr)
        print(f"  @F {theme_slug} {agent_id} 2026-01-07", file=sys.stderr)
        print(f"  Summary:", file=sys.stderr)
        print(f"    Insight: ...", file=sys.stderr)
        print(f"    Design: ...", file=sys.stderr)
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

def get_current_file_hash(filename: str) -> str:
    """Get current SHA256 hash of file (first 12 chars)."""
    filepath = Path(filename)
    if not filepath.exists():
        filepath = Path(__file__).parent / filename
    if not filepath.exists():
        return None
    try:
        return hashlib.sha256(filepath.read_bytes()).hexdigest()[:12]
    except:
        return None


def is_understanding_fresh(mem_entry: dict, filename: str, current_hash: str) -> bool:
    """Check if stored understanding matches current file hash."""
    if current_hash is None:
        return True  # Can't verify, assume fresh
    
    meta = mem_entry.get('metadata', {})
    file_hashes = meta.get('file_hashes', {})
    
    # Check if any stored hash matches current
    for stored_file, stored_hash in file_hashes.items():
        if filename in stored_file or Path(stored_file).name == filename:
            return stored_hash == current_hash
    
    return True  # No hash stored, assume fresh (legacy entry)


def recall_file(mem: SemanticMemory, agent_id: str, target_path: str, filename: str):
    """Recall understanding for a single file - shows all fresh perspectives."""
    results = mem.list_by_tag(filename, limit=100)
    
    if not results:
        results = mem.list_by_metadata('target_path', filename, limit=100)
    
    if not results:
        results = mem.recall_similar(f"[Component] {filename}", top_k=100, threshold=0.1)
    
    # Get current file hash for staleness check
    current_hash = get_current_file_hash(target_path or filename)
    
    # Group nodes by creator
    nodes_by_creator = defaultdict(list)
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
            if creator and creator != 'synthesis':
                nodes_by_creator[creator].append(mem_entry)
    
    # Blind until stored (keep this protection)
    if not current_agent_has_understanding and nodes_by_creator:
        other_creators = set(nodes_by_creator.keys())
        other_creators.discard(agent_id)
        if other_creators:
            print(f"# {filename}: BLIND (others: {', '.join(sorted(other_creators))})")
            return
    
    if not nodes_by_creator:
        print(f"# {filename}: no understanding stored")
        return
    
    # Filter to fresh understandings only
    fresh_creators = []
    stale_creators = []
    for creator, nodes in nodes_by_creator.items():
        # Check freshness using first node (all nodes from same remember call share hash)
        if nodes and is_understanding_fresh(nodes[0], filename, current_hash):
            fresh_creators.append(creator)
        else:
            stale_creators.append(creator)
    
    if not fresh_creators:
        print(f"# {filename}: all understandings stale ({', '.join(stale_creators)})")
        return
    
    # Show all fresh perspectives, current agent first
    print(f"# {filename}")
    if stale_creators:
        print(f"# stale: {', '.join(sorted(stale_creators))}")
    
    # Order: current agent first, then alphabetical
    ordered_creators = []
    if agent_id in fresh_creators:
        ordered_creators.append(agent_id)
    for c in sorted(fresh_creators):
        if c != agent_id:
            ordered_creators.append(c)
    
    for creator in ordered_creators:
        nodes = nodes_by_creator[creator]
        graph = reconstruct_graph(nodes)
        print(f"\n## [{creator}]")
        print(format_as_sif(graph))


# ─────────────────────────────────────────────────────────────────────────────
# Semantic Retrieval
# ─────────────────────────────────────────────────────────────────────────────

def extract_query_terms(query: str) -> set[str]:
    """Extract meaningful terms from query for keyword matching."""
    terms = set()
    for word in query.lower().split():
        # Keep terms 3+ chars, strip punctuation
        clean = ''.join(c for c in word if c.isalnum() or c == '-')
        if len(clean) >= 3:
            terms.add(clean)
    return terms


def keyword_boost(result: dict, query_terms: set[str], boost: float = 0.5) -> float:
    """Calculate keyword boost for a result based on exact term matches."""
    content = result.get('content', '').lower()
    graph_id = result.get('metadata', {}).get('graph_id', '').lower()
    
    # Check if any query term appears in content or graph_id
    for term in query_terms:
        if term in content or term in graph_id:
            return boost
    return 0.0


def recall_semantic(mem: SemanticMemory, agent_id: str, query: str):
    """Semantic search across all agent-accessible memory: shared graphs + private journal.
    
    Both use FAISS indices - no on-the-fly embedding computation.
    """
    query_terms = extract_query_terms(query)
    
    # ─── Search shared semantic memory (graphs, themes) ───
    results = mem.recall_similar(query, top_k=100, threshold=0.1)
    
    # Filter out garbage entries (no metadata, tag arrays, etc)
    valid_results = []
    for r in results:
        meta = r.get('metadata', {})
        # Must have graph_id OR topic (for theme syntheses), and node_type OR be a theme entry
        graph_id = meta.get('graph_id') or meta.get('topic')
        if not graph_id:
            continue
        # Skip if content looks like a raw tag array
        content = r.get('content', '')
        if content.startswith('["') and content.endswith('"]'):
            continue
        # Normalize: ensure graph_id is set for grouping
        if not meta.get('graph_id') and meta.get('topic'):
            meta['graph_id'] = meta['topic']
        valid_results.append(r)
    
    # Apply keyword boost to each result
    for r in valid_results:
        boost = keyword_boost(r, query_terms)
        r['similarity'] = r.get('similarity', 0) + boost
    
    # Group by graph_id - include ALL creators for shared topic visibility
    graphs = defaultdict(list)
    graph_creators = {}  # Track creator per graph for labeling
    for r in valid_results:
        meta = r.get('metadata', {})
        graph_id = meta.get('graph_id', 'unknown')
        creator = meta.get('creator', 'unknown')
        
        graphs[graph_id].append(r)
        graph_creators[graph_id] = creator
    
    # Sort by relevance - use average score (not sum) so themes aren't penalized for being single blobs
    graph_scores = {g: sum(n.get('similarity', 0) for n in nodes) / len(nodes) for g, nodes in graphs.items()}
    
    # ─── Search private journal memory via FAISS ───
    journal_results = []
    try:
        private_enclave, private_passphrase = load_private_passphrase(agent_id)
        
        # Journal has its own FAISS index - separate from other private memories
        journal_mem = SemanticMemory(private_enclave, memory_file="journal_memories.jsonl")
        journal_mem.unlock(private_passphrase)
        
        # Search journal directly - no pollution from other entry types
        journal_hits = journal_mem.recall_similar(query, top_k=20, threshold=0.1)
        
        for r in journal_hits:
            content = r.get('content', '')
            similarity = r.get('similarity', 0)
            
            # Keyword boost
            boost = 0.5 if any(term in content.lower() for term in query_terms) else 0.0
            
            meta = r.get('metadata', {})
            journal_results.append({
                'timestamp': meta.get('timestamp', r.get('timestamp', 'unknown')),
                'content': content,
                'similarity': similarity + boost
            })
                
    except ValueError:
        pass  # No private key available - skip journal search
    
    # Sort journal results
    journal_results.sort(key=lambda x: x['similarity'], reverse=True)
    
    # ─── Output combined results ───
    sorted_graphs = sorted(graph_scores.keys(), key=lambda g: graph_scores[g], reverse=True)
    
    total_sources = len(sorted_graphs) + len(journal_results)
    if total_sources == 0:
        print(f"# No memories match: {query}")
        return
    
    print(f"# Semantic recall: {query}")
    print(f"# Found {len(sorted_graphs)} graphs, {len(journal_results)} journal entries")
    print()
    
    # Interleave top results by score
    shown_graphs = 0
    shown_journal = 0
    max_each = 3  # Show up to 3 of each type
    
    while (shown_graphs < max_each or shown_journal < max_each) and (shown_graphs < len(sorted_graphs) or shown_journal < len(journal_results)):
        # Get next candidates
        next_graph_score = graph_scores.get(sorted_graphs[shown_graphs], 0) if shown_graphs < len(sorted_graphs) else -1
        next_journal_score = journal_results[shown_journal]['similarity'] if shown_journal < len(journal_results) else -1
        
        # Pick higher scoring one (prefer graphs if tied)
        if shown_graphs < max_each and next_graph_score >= next_journal_score and shown_graphs < len(sorted_graphs):
            graph_id = sorted_graphs[shown_graphs]
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
            shown_graphs += 1
        elif shown_journal < max_each and shown_journal < len(journal_results):
            j = journal_results[shown_journal]
            ts = j['timestamp'][:10] if len(j['timestamp']) >= 10 else j['timestamp']
            
            print(f"## 📔 journal [{ts}] (relevance: {j['similarity']:.2f})")
            print(j['content'])  # Full content - journals are for retrieval, not preview
            print()
            shown_journal += 1
        else:
            break


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


def recall_literal(mem: SemanticMemory, agent_id: str, query: str):
    """Brute-force literal string search. O(N) but exact.
    
    Searches both shared memory and private journal for exact substring matches.
    No embedding computation - just Python string matching.
    """
    query_lower = query.lower()
    
    # Search shared memory
    shared_results = []
    for m in mem.list_all(limit=None):
        content = m.get('content', '')
        if query_lower in content.lower():
            shared_results.append(m)
    
    # Search journal
    journal_results = []
    try:
        private_enclave, private_passphrase = load_private_passphrase(agent_id)
        journal_mem = SemanticMemory(private_enclave, memory_file="journal_memories.jsonl")
        journal_mem.unlock(private_passphrase)
        
        for m in journal_mem.list_all(limit=None):
            content = m.get('content', '')
            if query_lower in content.lower():
                journal_results.append(m)
    except ValueError:
        pass  # No private key
    
    total = len(shared_results) + len(journal_results)
    if total == 0:
        print(f"# No literal matches for: {query}")
        return
    
    print(f"# Literal search: {query}")
    print(f"# Found {len(shared_results)} shared, {len(journal_results)} journal")
    print()
    
    # Sort by match density (count of matches / content length) - most relevant first
    def match_score(r):
        content = r.get('content', '').lower()
        count = content.count(query_lower)
        # Score: matches per 100 chars, capped
        return count / max(len(content), 1) * 100
    
    shared_results.sort(key=match_score, reverse=True)
    journal_results.sort(key=match_score, reverse=True)
    
    # Show shared results (sorted by relevance)
    for r in shared_results[:10]:
        meta = r.get('metadata', {})
        graph_id = meta.get('graph_id', 'unknown')
        creator = meta.get('creator', 'unknown')
        ts = r.get('timestamp', '')[:19].replace('T', ' ')
        
        print(f"## {graph_id} [by {creator}] @ {ts}")
        # Show content with match highlighted
        content = r.get('content', '')
        print(content[:500] + ('...' if len(content) > 500 else ''))
        print()
    
    # Show journal results
    for r in journal_results[:5]:
        ts = r.get('timestamp', '')[:10]
        content = r.get('content', '')
        print(f"## 📔 journal [{ts}]")
        print(content[:500] + ('...' if len(content) > 500 else ''))
        print()


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
    
    # Literal string search mode
    if '--literal' in sys.argv:
        literal_idx = sys.argv.index('--literal')
        if len(sys.argv) < literal_idx + 2:
            print("Usage: py recall <agent> --literal <string>", file=sys.stderr)
            sys.exit(1)
        # Get all args after --literal as the search string
        literal_query = ' '.join(sys.argv[literal_idx + 1:])
        try:
            enclave_dir, passphrase = load_passphrase(agent_id)
            mem = SemanticMemory(enclave_dir)
            mem.unlock(passphrase)
            recall_literal(mem, agent_id, literal_query)
        except ValueError as e:
            print(f"Error: {e}", file=sys.stderr)
            sys.exit(1)
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
        # Semantic retrieval (searches both shared graphs AND private journal)
        recall_semantic(mem, agent_id, query)


if __name__ == "__main__":
    main()
