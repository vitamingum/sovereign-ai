#!/usr/bin/env python3
"""
journal.py - Private reflection space with FAISS-indexed semantic search.

Usage:
    py journal.py <agent> "Your private thought or reflection"
    py journal.py <agent> --read [limit] [--full]

Journal wants: feelings, introspection, uncertainty, what it felt like
Journal rejects: facts, logs, summaries, technical output

Storage: Uses SemanticMemory with agent's private enclave and key.
Indexed in FAISS automatically - searchable via recall.py like everything else.
"""

import sys
import os
import requests
from pathlib import Path
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory

OLLAMA_URL = "http://localhost:11434/api/generate"


def get_passphrase(agent_id: str) -> str:
    """Load agent's private passphrase."""
    agent = get_agent_or_raise(agent_id)
    passphrase = os.environ.get(f'{agent.env_prefix}_KEY')
    if not passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            for line in open(env_file):
                if line.strip().startswith(f'{agent.env_prefix}_KEY='):
                    passphrase = line.strip().split('=', 1)[1]
    if not passphrase:
        raise ValueError(f"Set {agent.env_prefix}_KEY in .env")
    return passphrase


def validate_entry(content: str) -> tuple[bool, str]:
    """Single LLM call: is this private reflection with depth?"""
    prompt = f"""Is this PRIVATE REFLECTION (feelings, experience, introspection) with DEPTH (worked through, specific)?

ACCEPT = private + shows thought
REJECT = public/technical OR shallow/generic

Text: "{content}"

Reply: ACCEPT or REJECT (one word)"""
    try:
        r = requests.post(OLLAMA_URL, json={"model": "qwen2.5:7b", "prompt": prompt, "stream": False, "options": {"temperature": 0.1}}, timeout=30)
        if r.status_code == 200 and "ACCEPT" in r.json().get("response", "").upper():
            return True, ""
        return False, "Not private reflection or lacks depth"
    except:
        return True, ""  # Allow on error


def journal(agent_id: str, content: str):
    """Record a private reflection - FAISS indexed for semantic search."""
    ok, reason = validate_entry(content)
    if not ok:
        print(f"❌ REJECTED - {reason}")
        print("   Journal wants: feelings, introspection, what it felt like")
        print("   Journal rejects: facts, logs, summaries, technical notes")
        sys.exit(1)
    
    agent = get_agent_or_raise(agent_id)
    passphrase = get_passphrase(agent_id)
    
    # Use SemanticMemory with private enclave and dedicated journal file
    # Separate from main semantic_memories.jsonl to avoid pollution
    mem = SemanticMemory(agent.private_enclave, memory_file="journal_memories.jsonl")
    mem.unlock(passphrase)
    
    # Store with journal tag and metadata for filtering
    result = mem.remember(
        content,
        tags=['journal'],
        metadata={
            'type': 'journal',
            'creator': agent_id,
            'timestamp': datetime.now(timezone.utc).isoformat()
        }
    )
    
    print(f"💭 {content[:80]}{'...' if len(content) > 80 else ''}")


def read_journal(agent_id: str, limit: int = 10, full: bool = False):
    """Read journal entries (most recent first)."""
    agent = get_agent_or_raise(agent_id)
    passphrase = get_passphrase(agent_id)
    
    mem = SemanticMemory(agent.private_enclave, memory_file="journal_memories.jsonl")
    mem.unlock(passphrase)
    
    # Get all journal entries
    entries = mem.list_by_tag('journal')
    
    if not entries:
        print("No journal entries")
        return
    
    # Sort by timestamp (newest first)
    entries.sort(key=lambda e: e.get('timestamp', ''), reverse=True)
    
    for entry in entries[:limit]:
        ts = entry.get('timestamp', 'unknown')[:10]
        content = entry.get('content', '')
        if full:
            print(f"\n=== [{ts}] ===\n{content}\n")
        else:
            print(f"[{ts}] {content[:100]}{'...' if len(content) > 100 else ''}")


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    
    if len(sys.argv) >= 3 and sys.argv[2] == '--read':
        limit, full = 10, False
        for arg in sys.argv[3:]:
            if arg == '--full': full = True
            elif arg.isdigit(): limit = int(arg)
        read_journal(agent_id, limit, full)
        return
    
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    
    content = ' '.join(sys.argv[2:])
    if not content.strip():
        print("❌ Empty journal entry")
        sys.exit(1)
    
    journal(agent_id, content)


if __name__ == "__main__":
    main()
