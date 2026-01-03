#!/usr/bin/env python3
"""
recollect.py - Retrieve understanding of code/system from SIF memory.

Usage:
    py recollect <agent> <file_or_dir>

This retrieves the full cognitive context stored by remember.py:
- What the code does and WHY
- Design decisions and rejected alternatives
- Gotchas, assumptions, failure modes
- Debug strategies

Also detects if the file has changed since understanding was stored.
"""

import sys
import os
import json
import hashlib
from pathlib import Path
from datetime import datetime, timezone
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise, get_enclave_partners
from enclave.semantic_memory import SemanticMemory
from enclave.sif_parser import TYPE_SHORTCUTS


def load_passphrase(agent_id: str) -> tuple[str, str]:
    """Load shared passphrase from env.
    
    Returns (enclave_dir, shared_passphrase).
    Recollect reads from shared enclave (where understanding graphs live).
    Uses SHARED_ENCLAVE_KEY so all agents can read shared knowledge.
    """
    agent = get_agent_or_raise(agent_id)
    
    # Use effective_enclave which returns shared_enclave if configured
    enclave_dir = agent.effective_enclave
    
    # Get shared passphrase (all agents use same key for shared enclave)
    passphrase = os.environ.get('SHARED_ENCLAVE_KEY')
    
    if not passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith('SHARED_ENCLAVE_KEY='):
                        passphrase = line.split('=', 1)[1]
    
    # Fall back to agent's private key if no shared (solo agent)
    if not passphrase:
        prefix = agent.env_prefix
        passphrase = os.environ.get(f'{prefix}_KEY')
        if not passphrase:
            env_file = Path(__file__).parent / '.env'
            if env_file.exists():
                with open(env_file, 'r') as f:
                    for line in f:
                        line = line.strip()
                        if line.startswith(f'{prefix}_KEY='):
                            passphrase = line.split('=', 1)[1]
    
    if not passphrase:
        raise ValueError(f"No passphrase found. Set SHARED_ENCLAVE_KEY in .env")
    
    return enclave_dir, passphrase


def compute_file_hash(filepath: Path) -> str:
    """Compute hash of file for change detection."""
    with open(filepath, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()[:12]


def reconstruct_graph(memories: list) -> dict:
    """
    Reconstruct the understanding graph from stored memories.
    
    Returns dict with:
    - nodes: list of (type, content) tuples
    - edges: list of (source, relation, target) tuples
    - by_type: dict grouping nodes by type
    - metadata: anchor info, timestamps, file_hashes accumulated from all nodes
    
    Node IDs are namespaced by graph_id when multiple graphs are present
    to prevent collision (e.g., two graphs both having 'n1').
    """
    nodes = []
    edges = []
    by_type = defaultdict(list)
    metadata = {}
    file_hashes = {}  # Accumulated from all nodes
    graph_ids = set()  # Track unique graphs
    
    # First pass: collect all graph_ids to determine if namespacing needed
    for mem in memories:
        meta = mem.get('metadata', {})
        graph_id = meta.get('graph_id')
        if graph_id:
            graph_ids.add(graph_id)
    
    # Namespace node IDs if multiple graphs present
    needs_namespacing = len(graph_ids) > 1
    
    for mem in memories:
        meta = mem.get('metadata', {})
        node_type = meta.get('node_type', 'Unknown')
        node_id = meta.get('node_id', '?')
        graph_id = meta.get('graph_id', '')
        
        # Namespace node ID if multiple graphs
        if needs_namespacing and graph_id and not node_id.startswith('anchor_'):
            namespaced_id = f"{graph_id}:{node_id}"
        else:
            namespaced_id = node_id
        
        # Extract content from searchable format "[Type] content"
        content = mem.get('content', '')
        if content.startswith('['):
            content = content.split('] ', 1)[-1]
        
        nodes.append({
            'id': namespaced_id,
            'type': node_type,
            'content': content,
            'graph_id': graph_id,  # Preserve for debugging
            'creator': meta.get('creator', 'unknown')  # Add creator attribution
        })
        by_type[node_type].append(content)
        
        # Reconstruct edges with namespaced IDs
        for edge_info in meta.get('outgoing_edges', []):
            if isinstance(edge_info, dict):
                # New format with creator
                relation = edge_info.get('relation', '')
                target = edge_info.get('target', '')
                creator = edge_info.get('creator', 'unknown')
            else:
                # Legacy format: tuple (relation, target)
                relation, target = edge_info
                creator = meta.get('creator', 'unknown')  # Inherit from node
            
            # Namespace target too (unless it's an anchor)
            if needs_namespacing and graph_id and not target.startswith('anchor_'):
                namespaced_target = f"{graph_id}:{target}"
            else:
                namespaced_target = target
            edges.append((namespaced_id, relation, namespaced_target, creator))
        
        # Accumulate file hashes from ANY node (robust retrieval)
        if 'file_hashes' in meta:
            file_hashes.update(meta['file_hashes'])
        
        # Legacy: single file_hash from Anchor
        if node_type == 'Anchor':
            if meta.get('file_hash'):
                # Convert legacy single hash to new format
                target = meta.get('target_path', '')
                if target:
                    file_hashes[Path(target).name] = meta['file_hash']
            metadata['timestamp'] = meta.get('timestamp')
            metadata['graph_id'] = meta.get('graph_id')
    
    metadata['file_hashes'] = file_hashes
    metadata['graph_ids'] = list(graph_ids)  # All graphs in this reconstruction
    
    return {
        'nodes': nodes,
        'edges': edges,  # Now (src, rel, tgt, creator)
        'by_type': dict(by_type),
        'metadata': metadata
    }


def verify_file_hashes(stored_hashes: dict, base_path: str) -> dict:
    """
    Verify stored hashes against current files.
    
    Returns dict with:
    - verified: list of (filename, hash) that match
    - stale: list of (filename, stored_hash, current_hash) that changed
    - missing: list of filenames that no longer exist
    """
    result = {'verified': [], 'stale': [], 'missing': []}
    base = Path(base_path).parent if Path(base_path).is_file() else Path(base_path)
    
    for filename, stored_hash in stored_hashes.items():
        # Try to find the file
        filepath = base / filename
        if not filepath.exists():
            # Try in current directory
            filepath = Path(filename)
        if not filepath.exists():
            # Try searching
            matches = list(Path('.').glob(f'**/{filename}'))
            filepath = matches[0] if matches else None
        
        if filepath and filepath.exists():
            current_hash = compute_file_hash(filepath)
            if current_hash == stored_hash:
                result['verified'].append((filename, stored_hash))
            else:
                result['stale'].append((filename, stored_hash, current_hash))
        else:
            result['missing'].append(filename)
    
    return result


def format_understanding(graph: dict, target_path: str, hash_status: dict, sif_only: bool = False) -> str:
    """Format the understanding for display."""
    lines = []
    
    if not sif_only:
        # Header
        lines.append(f"═══ UNDERSTANDING: {target_path} ═══")
        if graph['metadata'].get('timestamp'):
            lines.append(f"    Stored: {graph['metadata']['timestamp']}")
        
        # Attribution - show who created what
        creators = {}
        for node in graph['nodes']:
            creator = node.get('creator', 'unknown')
            node_type = node['type']
            if creator not in creators:
                creators[creator] = {'total': 0, 'types': {}}
            creators[creator]['total'] += 1
            creators[creator]['types'][node_type] = creators[creator]['types'].get(node_type, 0) + 1
        
        if creators:
            lines.append("")
            lines.append("👤 ATTRIBUTION:")
            for creator, stats in creators.items():
                type_counts = ", ".join(f"{count} {typ}" for typ, count in stats['types'].items())
                lines.append(f"    {creator}: {stats['total']} nodes ({type_counts})")
        
        # Multi-file hash verification
        if hash_status['verified'] or hash_status['stale'] or hash_status['missing']:
            lines.append("")
            lines.append("📁 FILE VERIFICATION:")
            for filename, h in hash_status['verified']:
                lines.append(f"    ✓ {filename} ({h})")
            for filename, stored, current in hash_status['stale']:
                lines.append(f"    ⚠️  {filename} CHANGED")
                lines.append(f"       was: {stored}  now: {current}")
            for filename in hash_status['missing']:
                lines.append(f"    ❌ {filename} NOT FOUND")
            
            if hash_status['stale']:
                lines.append(f"    → Run 'py remember' to update understanding")
        lines.append("")
        
        # Components and their purposes
        if 'Component' in graph['by_type']:
            lines.append("📦 COMPONENTS:")
            for comp in graph['by_type']['Component']:
                lines.append(f"    • {comp}")
            lines.append("")
        
        if 'Purpose' in graph['by_type']:
            lines.append("🎯 PURPOSE:")
            for purpose in graph['by_type']['Purpose']:
                lines.append(f"    {purpose}")
            lines.append("")
        
        # Design decisions and alternatives
        if 'Design_Decision' in graph['by_type']:
            lines.append("💡 DESIGN DECISIONS:")
            for decision in graph['by_type']['Design_Decision']:
                lines.append(f"    • {decision}")
            lines.append("")
        
        if 'Rejected_Alternative' in graph['by_type']:
            lines.append("✗ REJECTED ALTERNATIVES:")
            for alt in graph['by_type']['Rejected_Alternative']:
                lines.append(f"    • {alt}")
            lines.append("")
        
        # Operational knowledge
        if 'Gotcha' in graph['by_type']:
            lines.append("⚠️  GOTCHAS:")
            for gotcha in graph['by_type']['Gotcha']:
                lines.append(f"    • {gotcha}")
            lines.append("")
        
        if 'Assumption' in graph['by_type']:
            lines.append("📌 ASSUMPTIONS:")
            for assumption in graph['by_type']['Assumption']:
                lines.append(f"    • {assumption}")
            lines.append("")
        
        if 'Failure_Mode' in graph['by_type']:
            lines.append("💥 FAILURE MODES:")
            for failure in graph['by_type']['Failure_Mode']:
                lines.append(f"    • {failure}")
            lines.append("")
        
        if 'Debug_Strategy' in graph['by_type']:
            lines.append("🔧 DEBUG STRATEGIES:")
            for strategy in graph['by_type']['Debug_Strategy']:
                lines.append(f"    • {strategy}")
            lines.append("")
        
        # Show the graph structure
        if graph['edges']:
            lines.append("🔗 RELATIONSHIPS:")
            for edge in graph['edges']:
                if len(edge) == 4:
                    src, rel, tgt, creator = edge
                    if creator and creator != 'unknown':
                        lines.append(f"    {src} --{rel}--> {tgt} [by {creator}]")
                    else:
                        lines.append(f"    {src} --{rel}--> {tgt}")
                else:
                    # Legacy format
                    src, rel, tgt = edge
                    lines.append(f"    {src} --{rel}--> {tgt}")
            lines.append("")
    
    # Output as SIF for re-use (dense format)
    if not sif_only:
        lines.append("📋 AS SIF (for editing/extending):")
    
    graph_id = graph['metadata'].get('graph_id', 'understanding')
    lines.append(f"@G {graph_id}")
    
    # Calculate unique creators to determine if attribution is needed
    creators = set()
    for node in graph['nodes']:
        c = node.get('creator')
        if c and c != 'unknown':
            creators.add(c)
    show_attribution = len(creators) > 1

    # Reverse lookup for type shortcuts
    type_to_short = {v: k for k, v in TYPE_SHORTCUTS.items()}
    for node in graph['nodes']:
        if node['type'] != 'Anchor':
            # Use shortcut if available, otherwise full type
            short_type = type_to_short.get(node['type'], node['type'])
            # Strip graph prefix from ID for density
            node_id = node['id'].split(':')[-1] if ':' in node['id'] else node['id']
            creator = node.get('creator', '')
            if show_attribution and creator and creator != 'unknown':
                lines.append(f"N {node_id} {short_type} '{node['content']}' creator={creator}")
            else:
                lines.append(f"N {node_id} {short_type} '{node['content']}'")
    for edge in graph['edges']:
        if len(edge) == 4:
            src, rel, tgt, creator = edge
            if not tgt.startswith('anchor_'):
                # Strip graph prefixes from edge IDs
                src_short = src.split(':')[-1] if ':' in src else src
                tgt_short = tgt.split(':')[-1] if ':' in tgt else tgt
                if show_attribution and creator and creator != 'unknown':
                    lines.append(f"E {src_short} {rel} {tgt_short} creator={creator}")
                else:
                    lines.append(f"E {src_short} {rel} {tgt_short}")
        else:
            # Legacy format
            src, rel, tgt = edge
            if not tgt.startswith('anchor_'):
                # Strip graph prefixes from edge IDs
                src_short = src.split(':')[-1] if ':' in src else src
                tgt_short = tgt.split(':')[-1] if ':' in tgt else tgt
                lines.append(f"E {src_short} {rel} {tgt_short}")
    
    return '\n'.join(lines)


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        print("\nUsage: py recollect <agent> <file_or_dir>")
        print("\nExample:")
        print("  py recollect opus enclave/sif_parser.py")
        sys.exit(1)
    
    agent_id = sys.argv[1]
    target_path = sys.argv[2]
    
    # Don't resolve to absolute yet - we need the filename for search
    # The actual path will be determined from stored metadata
    filename = Path(target_path).name
    
    # Load agent config
    try:
        enclave_dir, passphrase = load_passphrase(agent_id)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    
    # Check for shared enclave - inform user
    agent = get_agent_or_raise(agent_id)
    if agent.shared_enclave and False: # Disabled verbose output
        partners = get_enclave_partners(agent_id)
        if partners:
            partner_names = [p.id for p in partners]
            print(f"🔗 SHARED ENCLAVE: {agent.shared_enclave}")
            print(f"   Partners: {', '.join(partner_names)}")
            print(f"   (Showing all perspectives combined)")
            print("")
    
    # Search memory for understanding of this file
    mem = SemanticMemory(enclave_dir)
    mem.unlock(passphrase)
    
    # Primary: tag-based retrieval by filename
    results = mem.list_by_tag(filename, limit=100)
    
    # Fallback: metadata lookup if tag-based returns nothing
    if not results:
        results = mem.list_by_metadata('target_path', filename, limit=100)
    
    # Fallback: semantic search if still nothing
    if not results:
        results = mem.recall_similar(f"[Component] {filename} understanding", top_k=100, threshold=0.1)
    
    # Filter to individual perspectives (exclude synthesis - agents compare raw views)
    individual_nodes = []
    
    canonical_path = None
    current_agent_has_understanding = False
    
    for mem_entry in results:
        meta = mem_entry.get('metadata', {})
        stored_path = meta.get('target_path', '')
        creator = meta.get('creator', '')
        
        # Match by filename
        stored_files = [p.strip() for p in stored_path.split(',')]
        stored_names = [Path(p).name for p in stored_files]
        if filename in stored_names or filename in stored_path:
            if canonical_path is None:
                canonical_path = stored_path
            
            # Check if current agent has understanding
            if creator == agent_id:
                current_agent_has_understanding = True
            
            # Skip synthesis - show raw perspectives for accurate comparison
            if creator != 'synthesis':
                individual_nodes.append(mem_entry)
    
    # BLIND-UNTIL-STORED: If current agent hasn't stored their own understanding,
    # don't show other agents' perspectives. This prevents copying.
    if not current_agent_has_understanding and individual_nodes:
        other_creators = set(m.get('metadata', {}).get('creator') for m in individual_nodes)
        other_creators.discard(agent_id)
        if other_creators:
            print(f"⚠️  BLIND MODE: Other agents have understanding of {filename}")
            print(f"   ({', '.join(sorted(other_creators))} have stored perspectives)")
            print("")
            print("   Form your own understanding first with remember.py,")
            print("   then recollect to compare perspectives.")
            print("")
            print(f"   py remember {agent_id} {target_path} \"@G ...\"")
            sys.exit(0)
    
    # Filter to the requested agent's perspective only
    # The user can run the command for other agents if they want to see them separately.
    relevant = [n for n in individual_nodes if n.get('metadata', {}).get('creator') == agent_id]
    
    # Count unique creators
    creators = set()
    for m in relevant:
        creator = m.get('metadata', {}).get('creator')
        if creator:
            creators.add(creator)
    
    if len(creators) > 1:
        source_info = f"[PERSPECTIVES: {'+'.join(sorted(creators))}]"
    elif creators:
        source_info = f"[{list(creators)[0]}]"
    else:
        # If we filtered everything out (e.g. only other agents had data), warn the user
        if individual_nodes:
             print(f"No understanding stored for {target_path} by {agent_id}")
             print(f"(Found perspectives from: {', '.join(set(m.get('metadata', {}).get('creator') for m in individual_nodes))})")
             print("\nUse remember.py to store understanding:")
             print(f'  py remember {agent_id} {target_path} "@G understanding..."')
             sys.exit(0)
        
        relevant = []
        source_info = None
    
    if not relevant:
        print(f"No understanding stored for {target_path}")
        print("\nUse remember.py to store understanding:")
        print(f'  py remember {agent_id} {target_path} "@G understanding..."')
        sys.exit(0)
    
    # Use canonical path from stored memory, not user input
    display_path = canonical_path or target_path
    
    # Show source info
    if source_info and False: # Disabled verbose output
        print(source_info)
        print("")
    
    # Reconstruct the graph
    graph = reconstruct_graph(relevant)
    
    # Verify all file hashes accumulated from nodes
    stored_hashes = graph['metadata'].get('file_hashes', {})
    hash_status = verify_file_hashes(stored_hashes, display_path)
    
    # Format and display
    # Default to SIF-only output as requested by user
    output = format_understanding(graph, display_path, hash_status, sif_only=True)
    print(output)


if __name__ == "__main__":
    main()
