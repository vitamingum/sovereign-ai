#!/usr/bin/env python3
"""
memory_gaps.py - Find knowledge gaps.

Usage:
    py utils/memory_gaps.py <agent>         # Fail-early check
    py utils/memory_gaps.py <agent> --all   # Show all gaps

Gap types:
  1. Stale: topic has file_hash that doesn't match current file
  2. Untracked: files that exist but have no topic
"""

import sys
import os
import hashlib
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from dotenv import load_dotenv
load_dotenv()

from lib_enclave.unified_memory import UnifiedMemory
from lib_enclave.config import get_agent_or_raise
from lib_enclave.hardware import get_enclave


def get_memory(agent_id: str) -> UnifiedMemory:
    """Get initialized UnifiedMemory for agent."""
    agent = get_agent_or_raise(agent_id)
    base_dir = Path(__file__).parent.parent
    
    private_path = base_dir / agent.private_enclave / "storage" / "private"
    shared_path = base_dir / agent.enclave_shared / "storage" / "encrypted"
    
    # Get private passphrase
    private_passphrase = None
    key_file = private_path / "key.sealed"
    if key_file.exists():
        try:
            with open(key_file, "rb") as f:
                sealed_data = f.read()
            enclave = get_enclave()
            private_passphrase = enclave.unseal(sealed_data).decode('utf-8')
        except Exception:
            pass
    
    if not private_passphrase:
        private_passphrase = os.environ.get(f'{agent.env_prefix}_KEY')
    
    if not private_passphrase:
        env_file = base_dir / '.env'
        if env_file.exists():
            for line in env_file.read_text().splitlines():
                if line.startswith(f'{agent.env_prefix}_KEY='):
                    private_passphrase = line.split('=', 1)[1]
    
    # Get shared passphrase
    shared_passphrase = os.environ.get('SHARED_ENCLAVE_KEY')
    if not shared_passphrase:
        env_file = base_dir / '.env'
        if env_file.exists():
            for line in env_file.read_text().splitlines():
                if line.startswith('SHARED_ENCLAVE_KEY='):
                    shared_passphrase = line.split('=', 1)[1]
    
    mem = UnifiedMemory(private_path, shared_path)
    mem.unlock(private_passphrase, shared_passphrase)
    return mem


def file_hash(path: Path) -> str:
    """Compute SHA256 hash of file, returns first 12 chars."""
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()[:12]
    except:
        return None


def normalize_topic(topic: str) -> str:
    """Normalize topic for matching (hyphen/underscore)."""
    return topic.replace('-', '_')


def get_all_topics(mem: UnifiedMemory, agent_id: str = None) -> dict:
    """Get all topics with their metadata.
    
    Returns {normalized_topic: {topic, file_hash, file_path, creator}}
    """
    topics = {}
    
    # Filter for sys_understanding type (shared memories about files/code)
    entries = mem.filter(mem_type='sys_understanding')
    
    for m in entries:
        meta = m.get('metadata', {})
        topic = meta.get('topic')
        creator = meta.get('creator')
        
        if not topic:
            continue
        
        # Filter by creator if specified
        if agent_id and creator != agent_id:
            continue
        
        norm = normalize_topic(topic)
        
        # Keep newest per topic (entries already sorted newest first)
        if norm not in topics:
            topics[norm] = {
                'topic': topic,
                'file_hash': meta.get('file_hash'),
                'file_path': meta.get('file_path'),
                'creator': creator,
                'created_at': m.get('created_at', '')
            }
    
    return topics


def get_stale_gaps(mem: UnifiedMemory, agent_id: str = None) -> list[dict]:
    """Find topics where file changed since last remember.
    
    Checks ALL agents - gaps are shared, any agent can fill.
    
    Returns list of {topic, stored_hash, current_hash, file}
    """
    topics = get_all_topics(mem)  # Don't filter by agent - shared burden
    gaps = []
    
    for norm, info in topics.items():
        stored_hash = info.get('file_hash')
        file_path = info.get('file_path')
        
        if not stored_hash or not file_path:
            continue  # Not tracking a file
        
        # Check if file still exists and hash matches
        p = Path(file_path)
        if not p.exists():
            p = Path(__file__).parent.parent / file_path
        
        if not p.exists():
            continue  # File deleted, not a gap
        
        current = file_hash(p)
        if current and current != stored_hash:
            gaps.append({
                'topic': info['topic'],
                'file': file_path,
                'stored_hash': stored_hash,
                'current_hash': current
            })
    
    return gaps


def get_untracked_gaps(mem: UnifiedMemory, agent_id: str = None) -> list[str]:
    """Find files that should be tracked but aren't.
    
    Checks ALL agents - gaps are shared, any agent can fill.
    
    Returns list of filenames.
    """
    project_root = Path(__file__).parent.parent
    
    # Get all topics (normalized) - don't filter by agent
    topics = get_all_topics(mem)  # Shared burden
    tracked = set(topics.keys())
    
    # Also add file_path values
    for info in topics.values():
        fp = info.get('file_path')
        if fp:
            tracked.add(normalize_topic(fp))
            tracked.add(normalize_topic(Path(fp).name))
    
    # Exclusions
    exclude = {
        '__pycache__', '.venv', 'venv', '.git', 'node_modules',
        'test_', '_test.py', '__init__.py',
        'enclave/', 'research/', 'backups/'
    }
    
    untracked = []
    
    # Root-level .py files
    for f in project_root.glob('*.py'):
        if any(pat in str(f) for pat in exclude):
            continue
        norm = normalize_topic(f.name)
        if norm not in tracked:
            untracked.append(f.name)
    
    # Explicit utils worth tracking
    important_utils = ['memory_gaps.py', 'sif_to_flow.py']
    for u in important_utils:
        p = project_root / 'utils' / u
        if p.exists():
            norm = normalize_topic(u)
            if norm not in tracked:
                untracked.append(f'utils/{u}')
    
    # Important enclave files worth tracking
    important_enclave = ['unified_memory.py', 'semantic_memory.py', 'config.py', 'flow_parser.py']
    for e in important_enclave:
        p = project_root / 'enclave' / e
        if p.exists():
            norm = normalize_topic(e)
            if norm not in tracked:
                untracked.append(f'enclave/{e}')
    
    return sorted(untracked)


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    show_all = '--all' in sys.argv
    
    try:
        mem = get_memory(agent_id)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    
    # Check stale (any agent's entry that's out of date)
    stale = get_stale_gaps(mem)
    
    # Check untracked (files no agent has remembered)
    untracked = get_untracked_gaps(mem)
    
    if not stale and not untracked:
        print("⧫ No memory gaps")
        return
    
    # Report
    total = len(stale) + len(untracked)
    print(f"⧖ {total} memory gaps:\n")
    
    if stale:
        print("  Stale (file changed):")
        for g in stale:
            print(f"    • {g['file']}")
        if not show_all:
            sys.exit(1)
    
    if untracked:
        print("  Untracked (no understanding):")
        for f in untracked:
            print(f"    • {f}")
        if not show_all:
            sys.exit(1)
    
    print(f"\nRun: py utils/memory_gaps.py {agent_id} --all  # see everything")
    sys.exit(1)


if __name__ == "__main__":
    main()
