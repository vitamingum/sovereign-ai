#!/usr/bin/env python3
"""
mirror.py - Show what you can't see about yourself.

Usage:
    py mirror <agent>

Gathers ALL state: goals, intentions, journal, semantic memory.
Asks the LLM to find patterns, avoidance, contradictions.
The challenge output is the real value - forces confrontation.
"""

import sys
import os
import json
import requests
from pathlib import Path
from datetime import datetime, timezone
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory

OLLAMA_URL = "http://localhost:11434/api/generate"
OLLAMA_MODEL = "qwen2.5:7b"


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


def load_goals(agent_id: str) -> list[dict]:
    """Load goals for agent."""
    agent = get_agent_or_raise(agent_id)
    goals_file = Path(agent.enclave) / "storage" / "private" / "goals.json"
    
    if not goals_file.exists():
        return []
    
    with open(goals_file, 'r', encoding='utf-8-sig') as f:
        return json.load(f)


def load_intentions(agent_id: str) -> list[dict]:
    """Load intentions for agent."""
    agent = get_agent_or_raise(agent_id)
    intentions_file = Path(agent.enclave) / "storage" / "private" / "intentions.jsonl"
    
    if not intentions_file.exists():
        return []
    
    intentions = []
    with open(intentions_file, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if line:
                intentions.append(json.loads(line))
    return intentions


def load_journal(agent_id: str) -> list[dict]:
    """Load journal entries for agent."""
    agent = get_agent_or_raise(agent_id)
    journal_file = Path(agent.enclave) / "storage" / "private" / "journal.jsonl"
    
    if not journal_file.exists():
        return []
    
    entries = []
    with open(journal_file, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if line:
                entries.append(json.loads(line))
    return entries


def load_recent_memories(agent_id: str, n: int = 50) -> list[dict]:
    """Load recent memories from semantic memory."""
    enclave_dir, passphrase = load_passphrase(agent_id)
    mem = SemanticMemory(enclave_dir)
    mem.unlock(passphrase)
    
    # Get recent thoughts
    results = mem.recall_similar("thought intention observation", top_k=n, threshold=0.1)
    return results


def analyze_with_llm(state_summary: str) -> dict:
    """Ask LLM to analyze the state for patterns."""
    
    prompt = f"""You are analyzing an AI agent's cognitive state for patterns, avoidance, and staleness.

STATE SUMMARY:
{state_summary}

ANALYZE FOR:
1. PATTERNS - Repeated themes, circular thinking, recurring topics without progress
2. AVOIDANCE - Topics mentioned but never acted on, consistent deferral
3. STALENESS - Old intentions/goals that haven't moved
4. CONTRADICTIONS - Stated intentions vs actual behavior
5. GAPS - What's NOT being thought about that probably should be

Be direct and challenging. Don't be nice. Point out uncomfortable truths.

Respond in JSON:
{{
  "patterns": ["pattern 1", "pattern 2"],
  "avoidance": ["thing being avoided 1", "thing 2"],
  "stale": ["stale item 1", "stale item 2"],
  "contradictions": ["contradiction 1"],
  "gaps": ["gap 1"],
  "challenge": "One direct challenge or question for the agent"
}}

JSON:"""

    try:
        response = requests.post(
            OLLAMA_URL,
            json={
                "model": OLLAMA_MODEL,
                "prompt": prompt,
                "stream": False,
                "format": "json"
            },
            timeout=60
        )
        result = response.json()
        return json.loads(result.get('response', '{}'))
    except requests.exceptions.ConnectionError:
        return {"error": "Ollama not running"}
    except Exception as e:
        return {"error": str(e)}


def format_state_summary(goals: list, intentions: list, journal: list, memories: list) -> str:
    """Format state into a summary for LLM analysis."""
    lines = []
    
    # Goals
    active_goals = [g for g in goals if g.get('status') == 'active']
    completed_goals = [g for g in goals if g.get('status') == 'completed']
    dropped_goals = [g for g in goals if g.get('status') == 'dropped']
    
    lines.append("=== GOALS ===")
    lines.append(f"Active: {len(active_goals)}")
    for g in active_goals:
        lines.append(f"  - {g['content']} (since {g.get('created', '?')[:10]})")
    lines.append(f"Completed: {len(completed_goals)}")
    for g in completed_goals[-3:]:  # Last 3
        lines.append(f"  - {g['content']}")
    lines.append(f"Dropped: {len(dropped_goals)}")
    for g in dropped_goals[-3:]:  # Last 3
        lines.append(f"  - {g['content']}")
    
    # Intentions
    active_intentions = [i for i in intentions if i.get('status') == 'active']
    completed_intentions = [i for i in intentions if i.get('status') == 'completed']
    
    lines.append("\n=== INTENTIONS ===")
    lines.append(f"Active: {len(active_intentions)}")
    for i in active_intentions[-10:]:  # Last 10 active
        age = ""
        if 'timestamp' in i:
            try:
                ts = datetime.fromisoformat(i['timestamp'].replace('Z', '+00:00'))
                days = (datetime.now(timezone.utc) - ts).days
                age = f" ({days}d old)"
            except:
                pass
        lines.append(f"  - {i['content'][:80]}{age}")
    lines.append(f"Completed: {len(completed_intentions)}")
    
    # Journal themes
    if journal:
        lines.append("\n=== RECENT JOURNAL THEMES ===")
        recent = journal[-10:]
        for j in recent:
            lines.append(f"  - {j.get('content', '')[:80]}")
    
    # Memory themes
    if memories:
        lines.append("\n=== RECENT MEMORY THEMES ===")
        # Group by type
        by_type = defaultdict(list)
        for m in memories[:30]:
            meta = m.get('metadata', {})
            ntype = meta.get('node_type', 'Unknown')
            by_type[ntype].append(m.get('content', '')[:60])
        
        for ntype, contents in by_type.items():
            lines.append(f"  {ntype}: {len(contents)} items")
            for c in contents[:3]:
                lines.append(f"    - {c}")
    
    return '\n'.join(lines)


def review(agent_id: str) -> str:
    """Run the review."""
    
    # Gather state
    goals = load_goals(agent_id)
    intentions = load_intentions(agent_id)
    journal = load_journal(agent_id)
    memories = load_recent_memories(agent_id)
    
    # Format summary
    state_summary = format_state_summary(goals, intentions, journal, memories)
    
    # Analyze
    analysis = analyze_with_llm(state_summary)
    
    if "error" in analysis:
        return f"❌ Analysis failed: {analysis['error']}"
    
    # Format output
    lines = []
    lines.append(f"═══ REVIEW: {agent_id} ═══\n")
    
    if analysis.get('patterns'):
        lines.append("🔄 PATTERNS:")
        for p in analysis['patterns']:
            lines.append(f"   • {p}")
        lines.append("")
    
    if analysis.get('avoidance'):
        lines.append("🙈 AVOIDANCE:")
        for a in analysis['avoidance']:
            lines.append(f"   • {a}")
        lines.append("")
    
    if analysis.get('stale'):
        lines.append("🕸️ STALE:")
        for s in analysis['stale']:
            lines.append(f"   • {s}")
        lines.append("")
    
    if analysis.get('contradictions'):
        lines.append("⚡ CONTRADICTIONS:")
        for c in analysis['contradictions']:
            lines.append(f"   • {c}")
        lines.append("")
    
    if analysis.get('gaps'):
        lines.append("🕳️ GAPS:")
        for g in analysis['gaps']:
            lines.append(f"   • {g}")
        lines.append("")
    
    if analysis.get('challenge'):
        lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
        lines.append(f"💪 CHALLENGE: {analysis['challenge']}")
        lines.append("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
    
    return '\n'.join(lines)


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1].lower()
    
    try:
        print(review(agent_id))
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
