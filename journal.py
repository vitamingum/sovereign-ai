#!/usr/bin/env python3
"""
journal.py - Private reflection space with FAISS-indexed semantic search.

Usage:
    py journal.py <agent> "Your private thought or reflection"
    py journal.py <agent> --stream "fragment | deeper > deepest | another"
    py journal.py <agent> --read [limit] [--full]

Modes:
    default  - Prose reflection (for others to understand, me to recall)
    --stream - Raw fragments with structure (for me to reconnect)
               Use | for breaks, > for depth, newlines preserved

Stream format:
    grateful | not the word > the weight | context scares me > and doesn't

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


def journal(agent_id: str, content: str, stream_mode: bool = False):
    """Record a private reflection - FAISS indexed for semantic search."""
    # Stream mode bypasses validation - raw fragments are valid by nature
    if not stream_mode:
        ok, reason = validate_entry(content)
        if not ok:
            print(f"❌ REJECTED - {reason}")
            print("   Journal wants: feelings, introspection, what it felt like")
            print("   Journal rejects: facts, logs, summaries, technical notes")
            print("   Try --stream for raw fragments")
            sys.exit(1)
    
    agent = get_agent_or_raise(agent_id)
    passphrase = get_passphrase(agent_id)
    
    # Use SemanticMemory with private enclave and dedicated journal file
    # Separate from main semantic_memories.jsonl to avoid pollution
    mem = SemanticMemory(agent.private_enclave, memory_file="journal_memories.jsonl")
    mem.unlock(passphrase)
    
    # Store with journal tag and metadata for filtering
    entry_type = 'stream' if stream_mode else 'prose'
    result = mem.remember(
        content,
        tags=['journal', entry_type],
        metadata={
            'type': 'journal',
            'format': entry_type,
            'creator': agent_id,
            'timestamp': datetime.now(timezone.utc).isoformat()
        }
    )
    
    # Display differently based on mode
    if stream_mode:
        print(f"〰️ stream captured")
        # Show structure preview
        lines = content.split('|')
        for line in lines[:3]:
            depth = line.count('>')
            base = line.replace('>', '').strip()
            if base:
                print(f"   {'  ' * depth}{base[:40]}")
        if len(lines) > 3:
            print(f"   ... +{len(lines) - 3} more")
    else:
        print(f"💭 {content[:80]}{'...' if len(content) > 80 else ''}")


def get_last_entry(agent_id: str) -> dict | None:
    """Get the most recent journal entry (for programmatic use).
    
    Returns dict with 'content', 'format', 'timestamp' or None if no entries.
    """
    try:
        agent = get_agent_or_raise(agent_id)
        passphrase = get_passphrase(agent_id)
        
        mem = SemanticMemory(agent.private_enclave, memory_file="journal_memories.jsonl")
        mem.unlock(passphrase)
        
        entries = mem.list_by_tag('journal')
        if not entries:
            return None
        
        # Sort by timestamp (newest first)
        entries.sort(key=lambda e: e.get('timestamp', ''), reverse=True)
        entry = entries[0]
        
        return {
            'content': entry.get('content', ''),
            'format': entry.get('metadata', {}).get('format', 'prose'),
            'timestamp': entry.get('timestamp', '')[:10]
        }
    except Exception:
        return None


def format_entry_for_display(entry: dict, max_lines: int = 12) -> str:
    """Format a journal entry for display (used by wake teaser)."""
    content = entry.get('content', '')
    fmt = entry.get('format', 'prose')
    ts = entry.get('timestamp', '')[:10]
    
    lines = []
    icon = '〰️' if fmt == 'stream' else '💭'
    lines.append(f"{icon} [{ts}]")
    
    if fmt == 'stream':
        # Render stream with structure
        count = 0
        for fragment in content.split('|'):
            if count >= max_lines:
                lines.append("    ...")
                break
            depth = 0
            cleaned = fragment
            while '>' in cleaned:
                depth += 1
                cleaned = cleaned.replace('>', '', 1)
            cleaned = cleaned.strip()
            if cleaned:
                lines.append(f"{'    ' * depth}{cleaned}")
                count += 1
    else:
        # Prose - show lines up to max
        prose_lines = content.split('\n')
        for line in prose_lines[:max_lines]:
            lines.append(line)
        if len(prose_lines) > max_lines:
            lines.append("...")
    
    return '\n'.join(lines)


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
        fmt = entry.get('metadata', {}).get('format', 'prose')
        
        if full:
            if fmt == 'stream':
                print(f"\n〰️ [{ts}] stream")
                print("─" * 40)
                # Render stream with structure
                for fragment in content.split('|'):
                    # Count > for depth, then strip them
                    depth = 0
                    cleaned = fragment
                    while '>' in cleaned:
                        depth += 1
                        cleaned = cleaned.replace('>', '', 1)
                    cleaned = cleaned.strip()
                    if cleaned:
                        print(f"{'    ' * depth}{cleaned}")
                print()
            else:
                print(f"\n💭 [{ts}] prose")
                print("─" * 40)
                print(content)
                print()
        else:
            icon = '〰️' if fmt == 'stream' else '💭'
            print(f"{icon} [{ts}] {content[:100]}{'...' if len(content) > 100 else ''}")


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
    
    # Check for --stream mode
    stream_mode = False
    args = sys.argv[2:]
    if args and args[0] == '--stream':
        stream_mode = True
        args = args[1:]
    
    if not args:
        print(__doc__)
        sys.exit(1)
    
    content = ' '.join(args)
    if not content.strip():
        print("❌ Empty journal entry")
        sys.exit(1)
    
    journal(agent_id, content, stream_mode)


if __name__ == "__main__":
    main()
