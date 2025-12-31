#!/usr/bin/env python3
"""
think.py - Store thought, spawn continuation, surface related memories.

Usage:
    py think <agent> "what you did | what's next"
    
The pipe (|) is mandatory. Every thought spawns the next intention.

Output:
    1. Confirmation of stored thought
    2. The spawned intention
    3. Related memories (full, no truncation)
"""

import sys
import os
import json
from pathlib import Path
from datetime import datetime, timezone

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
        raise ValueError(f"Set SOVEREIGN_PASSPHRASE or {prefix}_KEY")
    
    return enclave_dir, passphrase


def save_intention(enclave_path: Path, intention: dict):
    """Append a new intention."""
    intentions_file = enclave_path / "storage" / "private" / "intentions.jsonl"
    intentions_file.parent.mkdir(parents=True, exist_ok=True)
    
    with open(intentions_file, 'a', encoding='utf-8') as f:
        f.write(json.dumps(intention) + "\n")


def parse_input(text: str) -> tuple[str, str]:
    """
    Parse input into (content, continuation).
    Raises ValueError if pipe is missing.
    """
    if '|' not in text:
        raise ValueError(
            "Missing continuation. Format: 'what you did | what's next'\n"
            "The pipe (|) is mandatory. Every thought spawns the next intention."
        )
    
    parts = text.split('|', 1)
    content = parts[0].strip()
    continuation = parts[1].strip()
    
    if not content:
        raise ValueError("Content before | cannot be empty")
    if not continuation:
        raise ValueError("Continuation after | cannot be empty")
    
    return content, continuation


def think(agent_id: str, text: str) -> str:
    """
    Process input: store the content, spawn the continuation, show related.
    """
    base_dir = Path(__file__).parent
    enclave_dir, passphrase = load_passphrase(agent_id)
    enclave_path = base_dir / enclave_dir
    
    # Parse input
    content, continuation = parse_input(text)
    
    timestamp = datetime.now(timezone.utc).isoformat()
    
    # Initialize memory
    memory = SemanticMemory(enclave_path)
    memory.unlock(passphrase)
    
    # Store the content
    result = memory.remember(content, tags=['thought'])
    memory_id = result['id']
    
    # Create the continuation as an intention
    intention = {
        'id': f"int_{int(datetime.now(timezone.utc).timestamp() * 1000)}",
        'content': continuation,
        'spawned_from': memory_id,
        'spawned_from_content': content[:100],
        'timestamp': timestamp,
        'status': 'active'
    }
    save_intention(enclave_path, intention)
    
    # Build output
    output = []
    output.append(f"✓ Stored: {content}")
    output.append(f"→ Next: {continuation}")
    output.append("")
    
    # Find related memories (semantic search on what was just stored)
    related = memory.recall_similar(content, top_k=3, threshold=0.3)
    
    # Filter out the one we just stored
    related = [m for m in related if m['id'] != memory_id]
    
    if related:
        output.append("💭 RELATED:")
        for mem in related:
            # Full content, no truncation
            output.append(f"   • {mem['content']}")
    
    return '\n'.join(output)


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        print("\nExamples:")
        print('  py think opus "Found the bug in parsing | Fix it and test"')
        print('  py think opus "Sent message to Gemini | Wait for response"')
        sys.exit(1)
    
    agent_id = sys.argv[1]
    text = ' '.join(sys.argv[2:])
    
    try:
        print(think(agent_id, text))
    except ValueError as e:
        print(f"Error: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
