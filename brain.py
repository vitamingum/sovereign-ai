#!/usr/bin/env python3
"""
brain.py - One interface for sovereign thought.

Every interaction requires two parts: what you're doing | what's next
The pipe is mandatory. No continuation = error.

Usage:
    py brain.py <agent> "thought or action | next intention"
    
Examples:
    py brain.py opus "The theorem flaw is real | ASK Gemini if this changes their model"
    py brain.py opus "Sent message to Gemini | WAIT for response then critique"
    py brain.py opus "Built the new tool | TEST it on 5 queries"
    
The continuation becomes the next hot item in your intention queue.
"""

import sys
import os
import json
import re
from pathlib import Path
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.graph_memory import GraphMemory


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


def load_intentions(enclave_path: Path) -> list[dict]:
    """Load existing intentions from file."""
    intentions_file = enclave_path / "storage" / "private" / "intentions.jsonl"
    if not intentions_file.exists():
        return []
    
    intentions = []
    with open(intentions_file, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                intentions.append(json.loads(line))
    return intentions


def save_intention(enclave_path: Path, intention: dict):
    """Append a new intention."""
    intentions_file = enclave_path / "storage" / "private" / "intentions.jsonl"
    intentions_file.parent.mkdir(parents=True, exist_ok=True)
    
    with open(intentions_file, 'a', encoding='utf-8') as f:
        f.write(json.dumps(intention) + "\n")


def get_hot_intentions(enclave_path: Path, top_k: int = 5) -> list[dict]:
    """Get the hottest intentions based on recency and status."""
    intentions = load_intentions(enclave_path)
    
    # Filter to active (not completed) intentions
    active = [i for i in intentions if i.get('status') != 'completed']
    
    # Sort by timestamp (most recent first)
    active.sort(key=lambda x: x.get('timestamp', ''), reverse=True)
    
    return active[:top_k]


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


def detect_type(content: str) -> str:
    """Detect the type of content based on patterns."""
    content_lower = content.lower()
    
    # Message patterns
    if re.match(r'^(to |@|message |tell |ask )', content_lower):
        return 'message'
    if ':' in content and content.split(':')[0].lower() in ['gemini', 'gpt', 'grok', 'opus']:
        return 'message'
    
    # Action patterns  
    if re.match(r'^(built |created |fixed |deleted |ran |tested |pushed |committed )', content_lower):
        return 'action'
    
    # Default to thought
    return 'thought'


def brain(agent_id: str, text: str) -> dict:
    """
    Process input: store the content, spawn the continuation.
    Returns summary of what happened.
    """
    base_dir = Path(__file__).parent
    enclave_dir, passphrase = load_passphrase(agent_id)
    enclave_path = base_dir / enclave_dir
    
    # Parse input
    content, continuation = parse_input(text)
    content_type = detect_type(content)
    
    timestamp = datetime.now(timezone.utc).isoformat()
    
    # Store the content as a memory
    memory = GraphMemory(enclave_path)
    memory.unlock(passphrase)
    
    result = memory.remember(content, tags=[content_type])
    memory_id = result['id']
    
    # Auto-connect to recent memories
    memory.auto_connect(memory_id, threshold=0.5)
    
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
    
    return {
        'stored': content_type,
        'memory_id': memory_id,
        'intention': continuation,
        'intention_id': intention['id']
    }


def show_hot(agent_id: str) -> str:
    """Show current hot intentions."""
    base_dir = Path(__file__).parent
    enclave_dir, _ = load_passphrase(agent_id)
    enclave_path = base_dir / enclave_dir
    
    hot = get_hot_intentions(enclave_path)
    
    if not hot:
        return "No active intentions. Start with: py brain.py <agent> \"thought | next\""
    
    output = ["## 🔥 What's Hot\n"]
    for i in hot:
        source = i.get('spawned_from_content', '')[:50]
        if source:
            source = f"\n  (from: \"{source}...\")"
        output.append(f"→ {i['content']}{source}\n")
    
    return '\n'.join(output)


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    
    # If no content provided, show hot intentions
    if len(sys.argv) < 3:
        print(show_hot(agent_id))
        sys.exit(0)
    
    text = ' '.join(sys.argv[2:])
    
    try:
        result = brain(agent_id, text)
        print(f"✓ Stored {result['stored']}: {result['memory_id']}")
        print(f"→ Next: {result['intention']}")
    except ValueError as e:
        print(f"Error: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
