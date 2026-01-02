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

from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory


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


def reconstruct_graph(memories: list) -> dict:
    """
    Reconstruct the understanding graph from stored memories.
    
    Returns dict with:
    - nodes: list of (type, content) tuples
    - edges: list of (source, relation, target) tuples
    - by_type: dict grouping nodes by type
    - metadata: anchor info, timestamps, file_hashes accumulated from all nodes
    """
    nodes = []
    edges = []
    by_type = defaultdict(list)
    metadata = {}
    file_hashes = {}  # Accumulated from all nodes
    
    for mem in memories:
        meta = mem.get('metadata', {})
        node_type = meta.get('node_type', 'Unknown')
        node_id = meta.get('node_id', '?')
        
        # Extract content from searchable format "[Type] content"
        content = mem.get('content', '')
        if content.startswith('['):
            content = content.split('] ', 1)[-1]
        
        nodes.append({
            'id': node_id,
            'type': node_type,
            'content': content
        })
        by_type[node_type].append(content)
        
        # Reconstruct edges
        for relation, target in meta.get('outgoing_edges', []):
            edges.append((node_id, relation, target))
        
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
    
    return {
        'nodes': nodes,
        'edges': edges,
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


def format_understanding(graph: dict, target_path: str, hash_status: dict) -> str:
    """Format the understanding for display."""
    lines = []
    
    # Header
    lines.append(f"═══ UNDERSTANDING: {target_path} ═══")
    if graph['metadata'].get('timestamp'):
        lines.append(f"    Stored: {graph['metadata']['timestamp']}")
    
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
        for src, rel, tgt in graph['edges']:
            lines.append(f"    {src} --{rel}--> {tgt}")
        lines.append("")
    
    # Output as SIF for re-use
    lines.append("📋 AS SIF (for editing/extending):")
    graph_id = graph['metadata'].get('graph_id', 'understanding')
    lines.append(f"@G {graph_id}")
    for node in graph['nodes']:
        if node['type'] != 'Anchor':
            lines.append(f"N {node['id']} {node['type']} '{node['content']}'")
    for src, rel, tgt in graph['edges']:
        if not tgt.startswith('anchor_'):
            lines.append(f"E {src} {rel} {tgt}")
    
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
    
    # Search memory for understanding of this file
    mem = SemanticMemory(enclave_dir)
    mem.unlock(passphrase)
    
    # Search by filename (extracted above)
    # Semantic search with lower threshold to get more results
    results = mem.recall_similar(f"[Component] {filename} understanding", top_k=100, threshold=0.1)
    
    # Filter to only memories about this specific path
    relevant = []
    canonical_path = None  # Will be set from first matching stored_path
    for mem_entry in results:
        meta = mem_entry.get('metadata', {})
        stored_path = meta.get('target_path', '')
        # Match by filename - check if this file is in the stored path
        # Handles both single file and comma-separated multi-file
        stored_files = [p.strip() for p in stored_path.split(',')]
        stored_names = [Path(p).name for p in stored_files]
        if filename in stored_names or filename in stored_path:
            relevant.append(mem_entry)
            # Use the stored path (which is correct) not the user's potentially wrong input
            if canonical_path is None:
                canonical_path = stored_path
    
    if not relevant:
        print(f"No understanding stored for {target_path}")
        print("\nUse remember.py to store understanding:")
        print(f'  py remember {agent_id} {target_path} "@G understanding..."')
        sys.exit(0)
    
    # Use canonical path from stored memory, not user input
    display_path = canonical_path or target_path
    
    # Reconstruct the graph
    graph = reconstruct_graph(relevant)
    
    # Verify all file hashes accumulated from nodes
    stored_hashes = graph['metadata'].get('file_hashes', {})
    hash_status = verify_file_hashes(stored_hashes, display_path)
    
    # Format and display
    output = format_understanding(graph, display_path, hash_status)
    print(output)


if __name__ == "__main__":
    main()
