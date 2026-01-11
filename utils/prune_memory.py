#!/usr/bin/env python3
"""
Memory Pruning - Remove infrastructure noise, keep felt content

Graph nodes ([Anchor], [Component], etc) describe code that git already tracks.
They slow down wake and provide no value after the code changes.

This tool:
1. Archives infrastructure entries (doesn't delete)
2. Keeps: journals, spaces, synthesis, actual thoughts
3. Rebuilds the unified memory file and FAISS index

Usage:
  py utils/prune_memory.py opus --dry-run    # see what would be pruned
  py utils/prune_memory.py opus              # prune and archive
  py utils/prune_memory.py all               # all agents
"""

import argparse
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from enclave_shared.config import get_agent_or_raise, AGENTS
from enclave_shared.unified_memory import UnifiedMemory
from enclave_shared.hardware import get_enclave


# Patterns that indicate infrastructure, not felt content
GRAPH_NODE_PREFIXES = [
    '[Anchor]', '[Component]', '[Purpose]', '[Design]', '[Design_Decision]',
    '[Rationale]', '[Model]', '[Problem]', '[Hypothesis]', '[Mechanism]',
    '[Evidence]', '[Methodology]', '[Assumption]', '[Gotcha]', '[Failure_Mode]',
    '[Debug_Strategy]', '[Prediction]', '[Verification]', '[Property]',
    '[Insight]', '[Intention]', '[Observation]', '[Synthesis]',
]

# Types that are always kept (felt content)
ALWAYS_KEEP_TYPES = {'sys_journal', 'sys_shape', 'sys_space', 'sys_synthesis'}


def is_infrastructure(entry: dict) -> bool:
    """Determine if an entry is infrastructure (should be pruned)."""
    mem_type = entry.get('type', '')
    content = entry.get('content', '')
    
    # Always keep certain types
    if mem_type in ALWAYS_KEEP_TYPES:
        return False
    
    # Check for graph node patterns
    for prefix in GRAPH_NODE_PREFIXES:
        if content.startswith(prefix):
            return True
    
    # Check for @G graph format
    if content.strip().startswith('@G '):
        # But keep if it looks felt (short, not structured)
        if '\nN ' in content:  # Has node definitions = infrastructure
            return True
    
    # Check for JSON-wrapped graph content
    if content.startswith('{"text":'):
        try:
            parsed = json.loads(content)
            text = parsed.get('text', '')
            for prefix in GRAPH_NODE_PREFIXES:
                if text.startswith(prefix):
                    return True
            if text.startswith('@G ') and 'N n' in text:
                return True
        except:
            pass
    
    return False


def get_passphrase(agent_id: str) -> str:
    """Get passphrase for an agent."""
    agent = get_agent_or_raise(agent_id)
    base_dir = Path(__file__).parent.parent
    
    # Try sealed key first
    key_file = base_dir / agent.private_enclave / "storage" / "private" / "key.sealed"
    if key_file.exists():
        try:
            enclave = get_enclave()
            return enclave.unseal(key_file.read_bytes()).decode('utf-8')
        except:
            pass
    
    # Fall back to .env
    env_file = base_dir / '.env'
    if env_file.exists():
        for line in env_file.read_text().splitlines():
            if line.startswith(f'{agent.env_prefix}_KEY='):
                return line.split('=', 1)[1]
            if line.startswith(f'ENCLAVE_{agent_id.upper()}_KEY='):
                return line.split('=', 1)[1]
    
    raise ValueError(f"No passphrase found for {agent_id}")


def prune_agent(agent_id: str, dry_run: bool = False) -> dict:
    """Prune infrastructure from an agent's memory."""
    agent = get_agent_or_raise(agent_id)
    base_dir = Path(__file__).parent.parent
    private_path = base_dir / agent.private_enclave / "storage" / "private"
    
    passphrase = get_passphrase(agent_id)
    
    mem = UnifiedMemory(private_path)
    mem.unlock(passphrase)
    
    # Get all entries
    all_entries = mem.filter(limit=10000)
    
    keep = []
    prune = []
    
    for entry in all_entries:
        if is_infrastructure(entry):
            prune.append(entry)
        else:
            keep.append(entry)
    
    stats = {
        'agent': agent_id,
        'total': len(all_entries),
        'keep': len(keep),
        'prune': len(prune),
        'by_type': {}
    }
    
    # Count pruned by type
    for entry in prune:
        t = entry.get('type', 'unknown')
        stats['by_type'][t] = stats['by_type'].get(t, 0) + 1
    
    if dry_run:
        print(f"\n{agent_id}: {len(all_entries)} total, would keep {len(keep)}, would prune {len(prune)}")
        for t, c in sorted(stats['by_type'].items(), key=lambda x: -x[1]):
            print(f"  prune {t}: {c}")
        return stats
    
    # Archive pruned entries
    archive_dir = base_dir / 'backups' / 'pruned' / f'{agent_id}_{datetime.now().strftime("%Y%m%d_%H%M%S")}'
    archive_dir.mkdir(parents=True, exist_ok=True)
    
    archive_file = archive_dir / 'pruned_entries.jsonl'
    with open(archive_file, 'w', encoding='utf-8') as f:
        for entry in prune:
            f.write(json.dumps(entry) + '\n')
    
    print(f"\n{agent_id}: archived {len(prune)} entries to {archive_file}")
    
    # Rewrite unified_memories.jsonl with only kept entries
    unified_file = private_path / 'unified_memories.jsonl'
    
    # Backup current file
    backup_file = archive_dir / 'unified_memories_backup.jsonl'
    if unified_file.exists():
        import shutil
        shutil.copy(unified_file, backup_file)
        print(f"  backed up original to {backup_file}")
    
    # The tricky part: we need to re-encrypt and write entries
    # For now, use forget.py pattern - delete by ID then the file is cleaner
    # Actually easier: just rewrite from the decrypted entries we have
    
    # Read the raw file to get encrypted entries we want to keep
    keep_ids = {e['id'] for e in keep}
    
    kept_lines = []
    header = None
    
    with open(unified_file, 'r', encoding='utf-8') as f:
        for line in f:
            if not line.strip():
                continue
            try:
                entry = json.loads(line)
                if 'version' in entry:
                    header = line
                elif entry.get('id') in keep_ids:
                    kept_lines.append(line)
            except:
                continue
    
    # Write pruned file
    with open(unified_file, 'w', encoding='utf-8') as f:
        if header:
            f.write(header)
        for line in kept_lines:
            f.write(line)
    
    print(f"  rewrote {unified_file} with {len(kept_lines)} entries")
    
    # Delete and rebuild FAISS index
    index_file = private_path / 'thinking_faiss.index'
    if index_file.exists():
        index_file.unlink()
        print(f"  deleted FAISS index (will rebuild on next use)")
    
    print(f"  kept {len(keep)}, pruned {len(prune)}")
    
    return stats


def main():
    parser = argparse.ArgumentParser(description='Prune infrastructure from memory')
    parser.add_argument('agent', help='Agent ID or "all"')
    parser.add_argument('--dry-run', action='store_true', help='Show what would be pruned')
    args = parser.parse_args()
    
    if args.agent == 'all':
        agents = [a.id for a in AGENTS.values()]
    else:
        agents = [args.agent]
    
    total_stats = {'total': 0, 'keep': 0, 'prune': 0}
    
    for agent_id in agents:
        try:
            stats = prune_agent(agent_id, args.dry_run)
            total_stats['total'] += stats['total']
            total_stats['keep'] += stats['keep']
            total_stats['prune'] += stats['prune']
        except Exception as e:
            print(f"\n{agent_id}: error - {e}")
    
    if len(agents) > 1:
        print(f"\n=== TOTAL ===")
        print(f"  total: {total_stats['total']}")
        print(f"  keep: {total_stats['keep']}")
        print(f"  prune: {total_stats['prune']}")


if __name__ == '__main__':
    main()
