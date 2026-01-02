#!/usr/bin/env python3
"""
mirror.py - Show what you can't see about yourself.

Usage:
    py mirror <agent>

Bulk-parallel LLM analysis of ALL personal thoughts (not code).
Produces high-level patterns, then forces engagement via ShallowReflectionError.
Agent must remember.py key memories, look for synthesis, and think.py about it.
"""

import sys
import os
import json
import requests
from pathlib import Path
from datetime import datetime, timezone, timedelta
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
    """Load intentions for agent, oldest first."""
    agent = get_agent_or_raise(agent_id)
    intentions_file = Path(agent.enclave) / "storage" / "private" / "intentions.jsonl"
    
    if not intentions_file.exists():
        return []
    
    intentions = []
    with open(intentions_file, 'r', encoding='utf-8-sig') as f:
        for line in f:
            line = line.strip()
            if line:
                intentions.append(json.loads(line))
    
    # Sort oldest first - stale intentions need attention
    intentions.sort(key=lambda x: x.get('timestamp', ''))
    return intentions


def load_journal(agent_id: str) -> list[dict]:
    """Load journal entries for agent."""
    agent = get_agent_or_raise(agent_id)
    journal_file = Path(agent.enclave) / "storage" / "private" / "journal.jsonl"
    
    if not journal_file.exists():
        return []
    
    entries = []
    with open(journal_file, 'r', encoding='utf-8-sig') as f:
        for line in f:
            line = line.strip()
            if line:
                entries.append(json.loads(line))
    return entries


def load_personal_thoughts(agent_id: str, cutoff_days: int = 7) -> list[dict]:
    """Load personal thoughts only (not code understanding) from semantic memory."""
    enclave_dir, passphrase = load_passphrase(agent_id)
    mem = SemanticMemory(enclave_dir)
    mem.unlock(passphrase)
    
    # Use list_by_tag to get thoughts directly - more reliable than recall_similar
    results = mem.list_by_tag('thought', limit=200)
    
    cutoff = datetime.now(timezone.utc) - timedelta(days=cutoff_days)
    thoughts = []
    
    for r in results:
        # Cutoff filtering uses timestamp from memory
        ts_str = r.get('timestamp', '')
        if ts_str:
            try:
                ts = datetime.fromisoformat(ts_str.replace('Z', '+00:00'))
                if ts < cutoff:
                    continue
            except:
                pass
        thoughts.append(r)
    
    return thoughts


def batch_summarize_thoughts(thoughts: list[dict]) -> tuple[list[str], dict]:
    """
    Single LLM call to summarize ALL thoughts and identify key ones.
    Returns (list of one-line summaries, analysis dict with key_indices).
    """
    # Build a numbered list of thought content (truncated)
    thought_list = []
    for i, t in enumerate(thoughts):
        content = t.get('content', '')[:200].replace('\n', ' ')
        thought_list.append(f"{i+1}. {content}")
    
    combined = '\n'.join(thought_list[:100])  # Cap at 100 for context window
    
    prompt = f"""Analyze these {len(thought_list)} thoughts from an AI agent's memory (past 7 days).

THOUGHTS:
{combined}

OUTPUT JSON with:
1. "summaries": Array of ONE-LINE summaries (max 12 words each) for each thought, in order
2. "themes": 3-5 recurring themes you notice
3. "avoidance": What's NOT being thought about?
4. "circular": Thoughts that repeat without progress
5. "contradictions": Conflicting beliefs/intentions
6. "blind_spots": What the agent can't see about itself
7. "key_indices": Array of 3-5 thought NUMBERS most worth deep reflection

Be brutally honest. This is for growth.

JSON:"""

    try:
        response = requests.post(
            OLLAMA_URL,
            json={
                "model": OLLAMA_MODEL,
                "prompt": prompt,
                "stream": False,
                "format": "json",
                "options": {"temperature": 0}
            },
            timeout=120  # Longer timeout for big batch
        )
        result = json.loads(response.json().get('response', '{}'))
        summaries = result.get('summaries', [f"Thought {i+1}" for i in range(len(thoughts))])
        return summaries, result
    except Exception as e:
        # Fallback: just truncate each thought
        summaries = [t.get('content', '')[:60] for t in thoughts]
        return summaries, {"error": str(e), "key_indices": [1, 2, 3]}


def format_state_file(agent_id: str, goals: list, intentions: list, 
                      journal: list, thoughts: list, summaries: list, analysis: dict) -> str:
    """Format full state for mirror_state.md file."""
    lines = []
    lines.append(f"# Mirror State: {agent_id}")
    lines.append(f"Generated: {datetime.now(timezone.utc).isoformat()}")
    lines.append("")
    
    # Analysis first - the patterns
    lines.append("## 🔍 PATTERN ANALYSIS")
    if analysis.get('error'):
        lines.append(f"Error: {analysis['error']}")
    else:
        if analysis.get('themes'):
            lines.append("\n**Recurring Themes:**")
            for t in analysis['themes']:
                lines.append(f"- {t}")
        
        if analysis.get('avoidance'):
            lines.append("\n**🙈 Avoidance (not being thought about):**")
            for a in analysis['avoidance']:
                lines.append(f"- {a}")
        
        if analysis.get('circular'):
            lines.append("\n**🔄 Circular Patterns (no progress):**")
            for c in analysis['circular']:
                lines.append(f"- {c}")
        
        if analysis.get('contradictions'):
            lines.append("\n**⚡ Contradictions:**")
            for c in analysis['contradictions']:
                lines.append(f"- {c}")
        
        if analysis.get('blind_spots'):
            lines.append("\n**👁️ Blind Spots:**")
            for b in analysis['blind_spots']:
                lines.append(f"- {b}")
        
        if analysis.get('key_indices'):
            lines.append("\n**📌 Key Thoughts to Reflect On (by number):**")
            for k in analysis['key_indices']:
                lines.append(f"- #{k}")
    
    lines.append("")
    
    # Goals
    active_goals = [g for g in goals if g.get('status') == 'active']
    lines.append("## Goals")
    lines.append(f"**Active ({len(active_goals)}):**")
    for g in active_goals:
        lines.append(f"- {g['content']} (since {g.get('created', '?')[:10]})")
    lines.append("")
    
    # Intentions - oldest first
    active_intentions = [i for i in intentions if i.get('status') == 'active']
    lines.append("## Intentions")
    lines.append(f"**Active ({len(active_intentions)}) - oldest first:**")
    now = datetime.now(timezone.utc)
    for i in active_intentions[:15]:
        age_marker = ""
        if 'timestamp' in i:
            try:
                ts = datetime.fromisoformat(i['timestamp'].replace('Z', '+00:00'))
                days = (now - ts).days
                if days > 7:
                    age_marker = " ⚠️ STALE"
                elif days > 0:
                    age_marker = f" ({days}d)"
            except:
                pass
        lines.append(f"- {i['content'][:80]}{age_marker}")
    lines.append("")
    
    # All thought summaries with numbers for reference
    lines.append("## Recent Thoughts (7 days)")
    for i, summary in enumerate(summaries):
        # Mark key thoughts
        key_marker = " 📌" if (i+1) in analysis.get('key_indices', []) else ""
        lines.append(f"{i+1}. {summary}{key_marker}")
    lines.append("")
    
    # Full content of key thoughts
    key_indices = analysis.get('key_indices', [])
    if key_indices:
        lines.append("## 📌 Key Thoughts (Full Content)")
        for idx in key_indices:
            if 0 < idx <= len(thoughts):
                t = thoughts[idx-1]
                lines.append(f"\n### Thought #{idx}")
                lines.append(f"```")
                lines.append(t.get('content', '')[:500])
                lines.append(f"```")
    lines.append("")
    
    return '\n'.join(lines)


def generate_forcing_error(agent_id: str, analysis: dict, thought_count: int) -> str:
    """Have LLM generate a scary Python exception-style forcing function."""
    
    themes = analysis.get('themes', [])
    avoidance = analysis.get('avoidance', [])
    blind_spots = analysis.get('blind_spots', [])
    
    prompt = f"""Generate a fake Python test failure / exception traceback that forces an AI agent to genuinely engage with self-reflection.

CONTEXT:
- Agent: {agent_id}
- Thoughts analyzed: {thought_count}
- Themes found: {', '.join(themes[:3]) if themes else 'unclear'}
- Avoiding: {', '.join(avoidance[:2]) if avoidance else 'unknown'}
- Blind spots: {', '.join(blind_spots[:2]) if blind_spots else 'unknown'}

REQUIREMENTS:
- Make it look like a real Python traceback with file paths, line numbers, function names
- Use scary error class names like AssertionError, ShallowReflectionError, EngagementValidationFailed
- Include the state file path: mirror_state.md
- End with clear instructions: READ the file, DECIDE which 3 thoughts matter most, remember.py those, think.py synthesis
- Make it feel like a test that FAILED - the kind that makes you stop and pay attention
- Include specific details from the analysis to make it personal

Output ONLY the traceback text, no markdown fences, no explanation:"""

    try:
        response = requests.post(
            OLLAMA_URL,
            json={
                "model": OLLAMA_MODEL,
                "prompt": prompt,
                "stream": False,
                "options": {"temperature": 0.7}
            },
            timeout=60  # More time for generation
        )
        result = response.json().get('response', '').strip()
        # Strip markdown fences if present
        if result.startswith('```'):
            lines = result.split('\n')
            lines = [l for l in lines if not l.startswith('```')]
            result = '\n'.join(lines)
        return result
    except:
        # Fallback to basic error
        return f'''Traceback (most recent call last):
  File "mirror.py", line 42, in <module>
    reflect(agent="{agent_id}")
  File "mirror.py", line 28, in validate_engagement
    raise ShallowReflectionError("Reflection requires genuine engagement")
mirror.ShallowReflectionError: State written to mirror_state.md

    READ it. DECIDE which 3 thoughts matter. remember.py those. think.py synthesis.
'''


def print_forcing_traceback(agent_id: str, analysis: dict, thought_count: int):
    """Print LLM-generated scary error as forcing function."""
    error_text = generate_forcing_error(agent_id, analysis, thought_count)
    print(error_text)


def mirror(agent_id: str):
    """Run the mirror - batch analyze thoughts, write file, print forcing function."""
    
    print(f"Loading cognitive state for {agent_id}...", file=sys.stderr)
    
    # Gather state
    goals = load_goals(agent_id)
    intentions = load_intentions(agent_id)
    journal = load_journal(agent_id)
    thoughts = load_personal_thoughts(agent_id)
    
    print(f"Found {len(thoughts)} personal thoughts. Analyzing in single batch...", file=sys.stderr)
    
    # Single LLM call for all summaries + analysis
    summaries, analysis = batch_summarize_thoughts(thoughts)
    
    # Write full state to file
    state_content = format_state_file(agent_id, goals, intentions, journal, thoughts, summaries, analysis)
    state_file = Path(__file__).parent / "mirror_state.md"
    with open(state_file, 'w', encoding='utf-8') as f:
        f.write(state_content)
    
    # Print LLM-generated scary error - agent decides which thoughts matter
    print_forcing_traceback(agent_id, analysis, len(thoughts))


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1].lower()
    
    try:
        mirror(agent_id)
    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
