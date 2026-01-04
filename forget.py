#!/usr/bin/env python3
"""
forget.py - Delete memories from semantic storage.

Usage:
    py forget.py <agent> --theme <topic>              # Delete theme by this agent
    py forget.py <agent> --theme <topic> --all        # Delete theme by ALL agents
    py forget.py <agent> --file <path>                # Delete file understanding
    py forget.py <agent> --id <memory_id>             # Delete specific memory by ID

Examples:
    py forget.py opus --theme sif-compression-density
    py forget.py opus --theme old-topic --all
    py forget.py opus --file deprecated.py
    py forget.py opus --id abc123

Forget enables:
- Theme replacement (delete old before storing new)
- Cleaning up orphaned/duplicate syntheses
- Removing stale file understanding
"""

import sys
import os
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory


def load_memory(agent_id: str) -> SemanticMemory:
    """Load and unlock semantic memory for agent."""
    agent = get_agent_or_raise(agent_id)
    
    if not agent.shared_enclave:
        raise ValueError(f"No shared_enclave configured for {agent_id}")
    
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
    
    sm = SemanticMemory(agent.shared_enclave)
    sm.unlock(passphrase)
    return sm


def forget_theme(agent_id: str, theme: str, all_agents: bool = False) -> int:
    """Delete theme synthesis. Returns count deleted."""
    sm = load_memory(agent_id)
    
    creator = None if all_agents else agent_id
    deleted = sm.forget(theme=theme, creator=creator)
    
    return deleted


def forget_file(agent_id: str, file_path: str) -> int:
    """Delete file understanding. Returns count deleted."""
    sm = load_memory(agent_id)
    
    # Find memories tagged with this file
    filename = Path(file_path).name
    existing = sm.list_by_tag(filename, limit=200)
    
    # Filter to this creator's nodes
    ids_to_delete = set()
    for node in existing:
        meta = node.get('metadata', {})
        if meta.get('creator') == agent_id:
            ids_to_delete.add(node['id'])
    
    if ids_to_delete:
        return sm.delete_by_ids(ids_to_delete)
    return 0


def forget_id(agent_id: str, memory_id: str) -> int:
    """Delete specific memory by ID. Returns count deleted."""
    sm = load_memory(agent_id)
    return sm.forget(id=memory_id)


def main():
    if len(sys.argv) < 4:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    
    # Parse flags
    theme = None
    file_path = None
    memory_id = None
    all_agents = "--all" in sys.argv
    
    args = sys.argv[2:]
    i = 0
    while i < len(args):
        if args[i] == "--theme" and i + 1 < len(args):
            theme = args[i + 1]
            i += 2
        elif args[i] == "--file" and i + 1 < len(args):
            file_path = args[i + 1]
            i += 2
        elif args[i] == "--id" and i + 1 < len(args):
            memory_id = args[i + 1]
            i += 2
        elif args[i] == "--all":
            i += 1
        else:
            i += 1
    
    # Execute forget
    try:
        if theme:
            deleted = forget_theme(agent_id, theme, all_agents)
            scope = "all agents" if all_agents else agent_id
            if deleted > 0:
                print(f"🗑️  Deleted {deleted} '{theme}' memories (by {scope})")
            else:
                print(f"No '{theme}' memories found (by {scope})")
        
        elif file_path:
            deleted = forget_file(agent_id, file_path)
            if deleted > 0:
                print(f"🗑️  Deleted {deleted} '{file_path}' memories (by {agent_id})")
            else:
                print(f"No '{file_path}' memories found (by {agent_id})")
        
        elif memory_id:
            deleted = forget_id(agent_id, memory_id)
            if deleted > 0:
                print(f"🗑️  Deleted memory {memory_id}")
            else:
                print(f"No memory with id '{memory_id}' found")
        
        else:
            print("Error: Specify --theme, --file, or --id")
            print(__doc__)
            sys.exit(1)
    
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
