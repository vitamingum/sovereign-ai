"""Instant stale memory detector - compare stored hashes to current files."""

import hashlib
import sys
from pathlib import Path
from table import render_table

def get_file_hash(filepath: Path) -> str:
    """Get first 12 chars of file hash."""
    try:
        return hashlib.sha256(filepath.read_bytes()).hexdigest()[:12]
    except (FileNotFoundError, PermissionError):
        return None

def get_remembered_files(agent: str) -> dict[str, str]:
    """Get all files with stored understanding and their anchored hashes."""
    enclave_path = Path(__file__).parent / f"enclave_{agent}" / "storage" / "private"
    memories_file = enclave_path / "semantic_memories.jsonl"
    
    if not memories_file.exists():
        return {}
    
    import json
    
    # Track file -> stored_hash from anchor nodes
    remembered = {}
    
    with open(memories_file, 'r', encoding='utf-8-sig') as f:
        for line in f:
            try:
                mem = json.loads(line.strip())
                content = mem.get('content', '')
                
                # Look for anchor nodes: anchor_<hash> with file reference
                # Format: [Anchor] Understanding of X.py at <hash>
                if '[Anchor]' in content and ' at ' in content:
                    # Parse: "[Anchor] Understanding of foo.py at abc123def456"
                    parts = content.split(' at ')
                    if len(parts) == 2:
                        hash_part = parts[1].strip()
                        # Extract filename from "Understanding of X"
                        file_part = parts[0].replace('[Anchor] Understanding of ', '')
                        if file_part:
                            remembered[file_part] = hash_part
            except:
                continue
    
    return remembered

def check_staleness(agent: str, project_root: Path = None) -> list[tuple[str, str, str, str]]:
    """Check all remembered files for staleness.
    
    Returns list of (filename, stored_hash, current_hash, status)
    """
    if project_root is None:
        project_root = Path(__file__).parent
    
    remembered = get_remembered_files(agent)
    results = []
    
    for filename, stored_hash in remembered.items():
        filepath = project_root / filename
        current_hash = get_file_hash(filepath)
        
        if current_hash is None:
            status = '❌ MISSING'
        elif current_hash == stored_hash:
            status = '✓ current'
        else:
            status = '⚠️ STALE'
        
        results.append((filename, stored_hash, current_hash or 'N/A', status))
    
    return results

def main():
    import argparse
    parser = argparse.ArgumentParser(description='Check for stale understanding')
    parser.add_argument('agent', help='Agent ID (opus, gemini, etc)')
    parser.add_argument('--all', action='store_true', help='Show all files, not just stale')
    parser.add_argument('--fail', action='store_true', help='Exit 1 if any stale files found')
    args = parser.parse_args()
    
    results = check_staleness(args.agent)
    
    if not results:
        print("No remembered files found.")
        return
    
    # Filter to just stale/missing unless --all
    if not args.all:
        results = [r for r in results if r[3] != '✓ current']
    
    if not results:
        print("✓ All understanding is current")
        return
    
    # Sort: stale first, then missing, then current
    order = {'⚠️ STALE': 0, '❌ MISSING': 1, '✓ current': 2}
    results.sort(key=lambda x: (order.get(x[3], 99), x[0]))
    
    rows = [[r[0], r[1], r[2], r[3]] for r in results]
    print(render_table(
        headers=['File', 'Stored', 'Current', 'Status'],
        rows=rows,
        style='rounded'
    ))
    
    stale_count = sum(1 for r in results if r[3] in ('⚠️ STALE', '❌ MISSING'))
    if stale_count > 0:
        print(f"\n⚠️  {stale_count} files need refresh.py → remember.py")
        if args.fail:
            sys.exit(1)

if __name__ == '__main__':
    main()
