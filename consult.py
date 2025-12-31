#!/usr/bin/env python3
"""
Consult memory before acting.

Before processing new input, check what you've already thought about similar things.
Uses semantic search + spreading activation for robust retrieval.

Usage:
    py consult.py <agent> "input text to check against memory"
    
Example:
    py consult.py opus "Gemini is asking about consciousness"
    py consult.py opus "Should I trust this approach?"
    
The output can be injected into your context before you respond.
"""

import sys
import os
from pathlib import Path
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.graph_memory import GraphMemory


def load_passphrase(agent_id: str) -> tuple[str, str]:
    """Load passphrase from env or .env file."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    
    # Check environment variables
    passphrase = os.environ.get(f'{prefix}_KEY') or os.environ.get('SOVEREIGN_PASSPHRASE')
    enclave_dir = os.environ.get(f'{prefix}_DIR') or agent.enclave
    
    # Try .env file
    if not passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith(f'{prefix}_KEY='):
                        passphrase = line.split('=', 1)[1]
                    elif line.startswith('SOVEREIGN_PASSPHRASE='):
                        passphrase = passphrase or line.split('=', 1)[1]
    
    if not passphrase:
        raise ValueError(f"Set SOVEREIGN_PASSPHRASE or {prefix}_KEY")
    
    return enclave_dir, passphrase


def consult(agent_id: str, query: str, top_k: int = 5, show_connections: bool = True) -> str:
    """
    Search memory for thoughts relevant to the query.
    
    Returns formatted string suitable for context injection.
    """
    base_dir = Path(__file__).parent
    enclave_dir, passphrase = load_passphrase(agent_id)
    
    memory = GraphMemory(base_dir / enclave_dir)
    memory.unlock(passphrase)
    
    # Use spreading activation for robust retrieval
    results = memory.recall_with_spreading(
        query, 
        top_k=top_k, 
        threshold=0.3,
        spread_depth=2,
        spread_decay=0.5
    )
    
    if not results:
        # Fall back to simple similarity
        results = memory.recall_similar(query, top_k=top_k, threshold=0.25)
        if not results:
            return f"No relevant memories found for: {query[:50]}..."
    
    output = []
    output.append(f"## Memory Consultation")
    output.append(f"**Query:** {query}")
    output.append(f"**Found:** {len(results)} relevant memories\n")
    
    for i, r in enumerate(results, 1):
        score = r.get('activation', r.get('similarity', 0))
        timestamp = r.get('timestamp', 'unknown')
        
        # Parse timestamp for relative time
        try:
            mem_time = datetime.fromisoformat(timestamp.replace('Z', '+00:00'))
            delta = datetime.now(timezone.utc) - mem_time
            if delta.days > 0:
                time_str = f"{delta.days} days ago"
            elif delta.seconds > 3600:
                time_str = f"{delta.seconds // 3600} hours ago"
            else:
                time_str = f"{delta.seconds // 60} minutes ago"
        except:
            time_str = timestamp
        
        content = r['content'].replace('\n', ' ')
        if len(content) > 500:
            content = content[:500] + "..."
        
        output.append(f"### [{i}] (score: {score:.2f}, {time_str})")
        output.append(f"> {content}")
        
        # Show connections if available and requested
        if show_connections and 'connections' in r and r['connections']:
            conn_summary = []
            for conn in r['connections'][:3]:
                conn_summary.append(f"{conn['type']}→{conn['target'][:12]}...")
            if conn_summary:
                output.append(f"*Connected to: {', '.join(conn_summary)}*")
        
        output.append("")
    
    return '\n'.join(output)


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    query = ' '.join(sys.argv[2:])
    
    try:
        result = consult(agent_id, query)
        print(result)
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
