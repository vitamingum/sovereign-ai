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

from enclave.semantic_memory import SemanticMemory
from enclave.config import get_agent_or_raise


def get_enclave_and_memory(agent_id: str):
    """Get shared enclave path and initialized SemanticMemory."""
    agent = get_agent_or_raise(agent_id)
    
    passphrase = os.environ.get('SHARED_ENCLAVE_KEY')
    if not passphrase:
        env_file = Path(__file__).parent.parent / '.env'
        if env_file.exists():
            for line in env_file.read_text().splitlines():
                if line.startswith('SHARED_ENCLAVE_KEY='):
                    passphrase = line.split('=', 1)[1]
    
    sm = SemanticMemory(agent.shared_enclave)
    sm.unlock(passphrase)
    return agent.shared_enclave, sm


def file_hash(path: Path) -> str:
    """Compute SHA256 hash of file, returns first 12 chars."""
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()[:12]
    except:
        return None


def normalize_topic(topic: str) -> str:
    """Normalize topic for matching (hyphen/underscore)."""
    return topic.replace('-', '_')


def get_all_topics(sm: SemanticMemory, agent_id: str = None) -> dict:
    """Get all topics with their metadata.
    
    Returns {normalized_topic: {topic, file_hash, file_path, creator}}
    """
    topics = {}
    
    for m in sm.list_all():
        meta = m.get('metadata', {})
        topic = meta.get('topic')
        creator = meta.get('creator')
        
        if not topic:
            continue
        
        # Filter by creator if specified
        if agent_id and creator != agent_id:
            continue
        
        norm = normalize_topic(topic)
        
        # Keep newest per topic
        stored_at = meta.get('stored_at', '')
        if norm not in topics or stored_at > topics[norm].get('stored_at', ''):
            topics[norm] = {
                'topic': topic,
                'file_hash': meta.get('file_hash'),
                'file_path': meta.get('file_path'),
                'creator': creator,
                'stored_at': stored_at
            }
    
    return topics


def get_stale_gaps(sm: SemanticMemory, agent_id: str = None) -> list[dict]:
    """Find topics where file changed since last remember.
    
    Returns list of {topic, stored_hash, current_hash, file}
    """
    topics = get_all_topics(sm, agent_id)
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


def get_untracked_gaps(sm: SemanticMemory, agent_id: str = None) -> list[str]:
    """Find files that should be tracked but aren't.
    
    Returns list of filenames.
    """
    project_root = Path(__file__).parent.parent
    
    # Get all topics (normalized)
    topics = get_all_topics(sm, agent_id)
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
    
    return sorted(untracked)


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    show_all = '--all' in sys.argv
    
    try:
        _, sm = get_enclave_and_memory(agent_id)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    
    # Check stale
    stale = get_stale_gaps(sm, agent_id)
    
    # Check untracked
    untracked = get_untracked_gaps(sm, agent_id)
    
    if not stale and not untracked:
        print("✅ No memory gaps")
        return
    
    # Report
    total = len(stale) + len(untracked)
    print(f"❌ {agent_id.capitalize()}: {total} items need attention")
    
    if stale:
        files = ', '.join(g['file'] for g in stale)
        print(f"N Stale '{files}'")
        print("# ^ file changed since last remember")
        if not show_all:
            sys.exit(1)
    
    if untracked:
        files = ', '.join(untracked)
        print(f"N Untracked '{files}'")
        print("# ^ remember OR delete")
        if not show_all:
            sys.exit(1)
    
    print(f"\nN Cmd 'py utils/memory_gaps.py {agent_id}'  # fail-early details")
    sys.exit(1)


if __name__ == "__main__":
    main()
