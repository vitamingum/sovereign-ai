#!/usr/bin/env python3
"""
reflect.py - Surface thoughts on a topic for agent synthesis

Usage: python reflect.py <agent> <topic>

Returns full thought content matching topic.
Agent synthesizes in-context, stores via think.py.
"""

import os
import sys
from pathlib import Path
from datetime import datetime, timezone
from dotenv import load_dotenv

load_dotenv()

sys.path.insert(0, str(Path(__file__).parent))
from enclave.semantic_memory import SemanticMemory


def load_passphrase(agent: str) -> tuple[Path, str]:
    """Load passphrase for agent's enclave."""
    enclave_dir = Path(__file__).parent / f"enclave_{agent}"
    
    # Try env patterns
    for pattern in [f"ENCLAVE_{agent.upper()}_KEY", f"{agent.upper()}_KEY"]:
        passphrase = os.environ.get(pattern)
        if passphrase:
            return enclave_dir, passphrase
    
    return enclave_dir, None


def get_thoughts_on_topic(agent: str, topic: str) -> list[dict]:
    """Get all thoughts matching topic."""
    enclave_dir, passphrase = load_passphrase(agent)
    if not passphrase:
        return []
    
    memory = SemanticMemory(enclave_dir)
    memory.unlock(passphrase)
    
    # Direct tag lookup - fast
    all_thoughts = memory.list_by_tag('thought', limit=100)
    
    # Score by topic relevance
    topic_lower = topic.lower()
    topic_words = set(topic_lower.split())
    
    scored = []
    for t in all_thoughts:
        content = t.get('content', '').lower()
        # Exact phrase match scores highest
        if topic_lower in content:
            score = 1.0
        else:
            content_words = set(content.split())
            overlap = len(topic_words & content_words)
            score = overlap / len(topic_words) if topic_words else 0
        if score > 0:
            scored.append((score, t))
    
    scored.sort(key=lambda x: -x[0])
    return [t for _, t in scored]


def extract_thought_content(raw: str) -> str:
    """Extract readable content from SIF thought.
    
    Handles both ; and \n as separators (think.py stores with ;).
    """
    # Handle both ; and \n as separators
    parts = raw.replace('\n', ';').split(';')
    parts = [p.strip() for p in parts]
    
    # Try plain text first
    text_lines = [p for p in parts if p and not p.startswith('@G ') and not p.startswith('N ') and not p.startswith('E ')]
    if text_lines:
        return '\n'.join(text_lines).strip()
    
    # Extract from SIF nodes
    node_content = []
    for p in parts:
        if p.startswith('N ') and "'" in p:
            start = p.find("'") + 1
            end = p.rfind("'")
            if start < end:
                node_content.append(p[start:end])
    
    return '\n'.join(node_content)


def format_age(ts: str) -> str:
    """Format timestamp as relative age."""
    try:
        dt = datetime.fromisoformat(ts.replace('Z', '+00:00'))
        now = datetime.now(timezone.utc)
        days = (now - dt).days
        if days == 0:
            return 'today'
        elif days == 1:
            return 'yesterday'
        else:
            return f'{days}d ago'
    except:
        return '?'


def main():
    if len(sys.argv) < 3:
        print("Usage: python reflect.py <agent> <topic>")
        print("       python reflect.py opus authenticity")
        sys.exit(1)
    
    agent = sys.argv[1]
    topic = ' '.join(sys.argv[2:])
    
    thoughts = get_thoughts_on_topic(agent, topic)
    
    if not thoughts:
        print(f"No thoughts on '{topic}'")
        sys.exit(0)
    
    print(f"═══ THOUGHTS ON: {topic.upper()} ({len(thoughts)} found) ═══\n")
    
    for i, t in enumerate(thoughts, 1):
        age = format_age(t.get('timestamp', ''))
        content = extract_thought_content(t.get('content', ''))
        print(f"[{i}] ({age})")
        print(content)
        print()
    
    print("─" * 40)
    print("Synthesize above, then: think.py opus \"<your synthesis SIF>\" 4")


if __name__ == '__main__':
    main()
