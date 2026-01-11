#!/usr/bin/env python3
"""
remember.py - Store understanding by topic.

Usage:
  py remember <agent> <topic> @content.flow
  py remember <agent> <topic> -              # stdin

Examples:
  py remember opus wake.py @wake.flow
  py remember opus encryption @encryption.flow
  py remember opus utils/memory_gaps.py @memory_gaps.flow
  cat my.flow | py remember opus some-topic -

Topic is just a string. If it matches an existing file path, we track the
file hash for staleness detection. If not, it's just a named concept.

Flow format only. Validates understanding depth before storing.
"""

import sys
import os
import hashlib
from pathlib import Path
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave_shared.config import get_agent_or_raise
from enclave_shared.unified_memory import UnifiedMemory
from enclave_shared.flow_parser import FlowParser, parse_flow, is_flow_format
from enclave_shared.hardware import get_enclave


# Critical topics that need higher node counts
# v4.3 format is ~25% denser, so thresholds adjusted down
CRITICAL_TOPICS = {
    'project-architecture': {'min_nodes': 30},
    'dev-tips': {'min_nodes': 8},
}


def load_passphrase(agent_id: str) -> tuple[Path, str, str]:
    """Load passphrases from env/sealed.
    
    Returns (base_dir, private_passphrase, shared_passphrase).
    """
    agent = get_agent_or_raise(agent_id)
    base_dir = Path(__file__).parent
    
    # Private passphrase
    private_path = base_dir / agent.private_enclave / "storage" / "private"
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
    
    if not private_passphrase:
        raise ValueError(f"No passphrase found for {agent_id}")
    
    # Shared passphrase
    shared_passphrase = os.environ.get('SHARED_ENCLAVE_KEY')
    if not shared_passphrase:
        env_file = base_dir / '.env'
        if env_file.exists():
            for line in env_file.read_text().splitlines():
                if line.startswith('SHARED_ENCLAVE_KEY='):
                    shared_passphrase = line.split('=', 1)[1]
    
    if not shared_passphrase:
        raise ValueError("No shared passphrase found. Set SHARED_ENCLAVE_KEY in .env")
    
    return base_dir, private_passphrase, shared_passphrase


def compute_file_hash(filepath: Path) -> str:
    """Compute SHA256 hash of file, returns first 12 chars."""
    if not filepath.exists():
        return None
    return hashlib.sha256(filepath.read_bytes()).hexdigest()[:12]


def resolve_file_path(topic: str) -> Path | None:
    """Check if topic matches an existing file path.
    
    Tries:
      1. Exact path from cwd
      2. Path relative to project root
    
    Returns Path if file exists, None otherwise.
    """
    # Try as-is
    p = Path(topic)
    if p.exists() and p.is_file():
        return p
    
    # Try from project root
    project_root = Path(__file__).parent
    p = project_root / topic
    if p.exists() and p.is_file():
        return p
    
    return None


def main():
    # Parse args
    if len(sys.argv) < 4:
        print(__doc__)
        print("\nUsage: py remember <agent> <topic> @content.flow")
        print("       py remember <agent> <topic> -  (stdin)")
        sys.exit(1)
    
    agent_id = sys.argv[1]
    topic = sys.argv[2]
    content_arg = sys.argv[3]
    
    # Read content
    if content_arg == '-':
        content = sys.stdin.read()
    elif content_arg.startswith('@') and len(content_arg) > 1:
        filepath = Path(content_arg[1:])
        if not filepath.exists():
            print(f"Error: File not found: {filepath}", file=sys.stderr)
            sys.exit(1)
        content = filepath.read_text(encoding='utf-8')
    else:
        content = content_arg
    
    content = content.strip()
    
    # Skip recall.py header lines (# and ## prefixes, or empty)
    lines = content.split('\n')
    while lines and (lines[0].startswith('#') or lines[0].strip() == ''):
        lines.pop(0)
    content = '\n'.join(lines).strip()
    
    if not content:
        print("Error: No content provided", file=sys.stderr)
        sys.exit(1)
    
    # Must be Flow format
    if not is_flow_format(content):
        print("Error: Content must be Flow format (start with @F)", file=sys.stderr)
        print("Example:")
        print("  @F topic agent date")
        print("  Summary:")
        print("    What: Brief description")
        print("    Purpose: Why it exists")
        sys.exit(1)
    
    # Parse Flow
    try:
        doc = parse_flow(content, creator=agent_id)
    except ValueError as e:
        print(f"❌ Flow parse error: {e}", file=sys.stderr)
        sys.exit(1)
    
    # Validate
    is_valid, errors = FlowParser.validate(doc)
    if not is_valid:
        print(f"❌ Flow validation failed:", file=sys.stderr)
        for err in errors[:5]:
            print(f"  - {err}", file=sys.stderr)
        sys.exit(1)
    
    # Check critical topic requirements
    topic_slug = topic.lower().replace(' ', '-').replace('_', '-')
    if topic_slug in CRITICAL_TOPICS:
        min_nodes = CRITICAL_TOPICS[topic_slug].get('min_nodes')
        if min_nodes and len(doc.nodes) < min_nodes:
            print(f"❌ CRITICAL: {topic} needs {min_nodes}+ nodes, got {len(doc.nodes)}", file=sys.stderr)
            sys.exit(1)
    
    # Check if topic is a file → compute hash
    file_path = resolve_file_path(topic)
    file_hash = None
    if file_path:
        file_hash = compute_file_hash(file_path)
    
    # Load memory
    try:
        base_dir, private_passphrase, shared_passphrase = load_passphrase(agent_id)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    
    agent = get_agent_or_raise(agent_id)
    private_path = base_dir / agent.private_enclave / "storage" / "private"
    shared_path = base_dir / agent.shared_enclave / "storage" / "encrypted"
    
    mem = UnifiedMemory(private_path, shared_path)
    mem.unlock(private_passphrase, shared_passphrase)
    
    # Delete previous understanding on this topic by this agent
    deleted = mem.delete_by_filter(
        mem_type='sys_understanding',
        metadata_match={'topic': topic_slug, 'creator': agent_id}
    )
    if deleted > 0:
        print(f"  🔄 Replaced {deleted} previous '{topic}' entries", file=sys.stderr)
    
    # Build metadata
    metadata = {
        "topic": topic_slug,
        "creator": agent_id,
        "format": "flow",
        "node_count": len(doc.nodes),
        "stored_at": datetime.now(timezone.utc).isoformat()
    }
    
    # Add file hash if topic is a file
    if file_hash:
        metadata["file_hash"] = file_hash
        metadata["file_path"] = str(file_path)
    
    # Store as sys_understanding (shared type)
    tags = ["topic", f"topic:{topic_slug}", "format:flow"]
    
    result = mem.store(
        content=content,
        mem_type='sys_understanding',
        tags=tags,
        metadata=metadata
    )
    
    # Output
    if file_hash:
        print(f"✅ Remembered: {topic} ({len(doc.nodes)} nodes, hash:{file_hash})")
    else:
        print(f"✅ Remembered: {topic} ({len(doc.nodes)} nodes)")
    
    # Show other agents' perspectives on the same topic
    show_other_perspectives(mem, topic_slug, agent_id, file_hash)


def show_other_perspectives(mem: UnifiedMemory, topic: str, current_agent: str, current_hash: str = None):
    """
    Show other agents' understanding of the same topic.
    
    Only shows fresh perspectives (matching file hash if topic is a file).
    Gives current agent visibility into how others interpreted the content.
    """
    all_memories = mem.filter(mem_type='sys_understanding')
    
    # Find other agents' understanding of this topic
    other_perspectives = {}  # agent -> content
    
    for m in all_memories:
        meta = m.get('metadata', {})
        stored_topic = meta.get('topic', '')
        creator = meta.get('creator', '')
        
        # Skip if not same topic or same agent
        if stored_topic != topic or creator == current_agent or not creator:
            continue
        
        # If this is a file topic, check hash freshness
        if current_hash:
            stored_hash = meta.get('file_hash', '')
            if stored_hash and stored_hash != current_hash:
                continue  # Stale - file changed since they wrote
        
        # Keep newest per agent
        stored_at = meta.get('stored_at', '')
        if creator not in other_perspectives or stored_at > other_perspectives[creator].get('stored_at', ''):
            other_perspectives[creator] = {
                'content': m.get('content', ''),
                'stored_at': stored_at,
                'node_count': meta.get('node_count', '?')
            }
    
    if not other_perspectives:
        return
    
    print(f"\n{'─' * 60}")
    print(f"📚 Other agents' perspectives on {topic}:")
    
    for agent, data in sorted(other_perspectives.items()):
        date = data['stored_at'][:10] if data['stored_at'] else '?'
        print(f"\n## [{topic}] by {agent} @ {date} ({data['node_count']} nodes)")
        print(data['content'])


if __name__ == "__main__":
    main()
