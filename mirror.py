#!/usr/bin/env python3
"""
mirror.py - Show what you can't see about yourself.

Usage:
    py mirror.py <agent> "question about your own behavior"
    py mirror.py <agent> --patterns              # general pattern analysis
    py mirror.py <agent> --read                  # show last mirror output

Examples:
    py mirror.py opus "when do I defer vs act?"
    py mirror.py opus "what triggers assistant-mode?"
    py mirror.py opus "how does my language change when exploring vs performing?"

Analyzes BOTH:
- Chat logs (what you actually did)
- Journal entries (what you said you thought)

The gap between them is where blind spots live.
Uses DeepSeek-R1 for reasoning-heavy self-analysis.
"""

import sys
import os
import json
import sqlite3
import requests
from pathlib import Path
from datetime import datetime, timezone, timedelta
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory

OLLAMA_URL = "http://localhost:11434/api/generate"
DEEPSEEK_MODEL = "deepseek-r1:14b"  # Reasoning model for self-analysis
FALLBACK_MODEL = "qwen2.5:7b"


def load_private_passphrase(agent_id: str) -> tuple[str, str]:
    """Load PRIVATE enclave passphrase.
    
    Mirror reads only private data (journal, private goals).
    """
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    
    # Use private_enclave - no fallback
    enclave_dir = agent.private_enclave
    
    # Get private passphrase - no fallback
    passphrase = os.environ.get(f'{prefix}_KEY')
    
    if not passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith(f'{prefix}_KEY='):
                        passphrase = line.split('=', 1)[1]
    
    if not passphrase:
        raise ValueError(f"No passphrase found. Set {prefix}_KEY in .env")
    
    return enclave_dir, passphrase


def load_chat_logs(agent_id: str, limit: int = 200) -> list[dict]:
    """Load chat logs from chat_index.db for this agent's model."""
    db_path = Path(__file__).parent / "data" / "chat_index.db"
    if not db_path.exists():
        return []
    
    # Map agent to model pattern
    model_patterns = {
        'opus': '%opus%',
        'gemini': '%gemini%',
        'gpt52': '%gpt%',
        'grok': '%grok%'
    }
    pattern = model_patterns.get(agent_id, f'%{agent_id}%')
    
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    cursor.execute("""
        SELECT timestamp, user_text, response_text 
        FROM requests 
        WHERE model_id LIKE ?
        ORDER BY timestamp DESC 
        LIMIT ?
    """, (pattern, limit))
    
    rows = cursor.fetchall()
    conn.close()
    
    return [
        {
            'timestamp': datetime.fromtimestamp(r[0]/1000, tz=timezone.utc).isoformat(),
            'user': r[1][:2000] if r[1] else '',  # Cap length
            'response': r[2][:2000] if r[2] else ''
        }
        for r in rows
    ]


def load_journal_entries(agent_id: str, limit: int = 50) -> list[dict]:
    """Load journal entries from private enclave."""
    agent = get_agent_or_raise(agent_id)
    enclave_dir, passphrase = load_private_passphrase(agent_id)
    
    try:
        mem = SemanticMemory(enclave_dir, memory_file="journal_memories.jsonl")
        mem.unlock(passphrase)
        entries = mem.list_by_tag('journal')
        entries.sort(key=lambda e: e.get('timestamp', ''), reverse=True)
        return entries[:limit]
    except Exception as e:
        print(f"Warning: Could not load journal: {e}", file=sys.stderr)
        return []


def semantic_search_chats(query: str, chats: list[dict], top_k: int = 15) -> list[dict]:
    """Simple keyword-based relevance for chat selection.
    
    TODO: Could use embedding similarity for better matching.
    """
    query_words = set(query.lower().split())
    
    scored = []
    for chat in chats:
        text = f"{chat.get('user', '')} {chat.get('response', '')}".lower()
        score = sum(1 for w in query_words if w in text)
        if score > 0:
            scored.append((score, chat))
    
    scored.sort(key=lambda x: -x[0])
    return [c for _, c in scored[:top_k]]


def semantic_search_journal(query: str, journal: list[dict], top_k: int = 10) -> list[dict]:
    """Simple keyword-based relevance for journal selection."""
    query_words = set(query.lower().split())
    
    scored = []
    for entry in journal:
        text = entry.get('content', '').lower()
        score = sum(1 for w in query_words if w in text)
        if score > 0:
            scored.append((score, entry))
    
    scored.sort(key=lambda x: -x[0])
    return [e for _, e in scored[:top_k]]
    
def format_context_for_analysis(query: str, chats: list[dict], journal: list[dict]) -> str:
    """Format chat logs and journal for DeepSeek analysis."""
    
    lines = []
    lines.append("=== SELF-ANALYSIS QUERY ===")
    lines.append(query)
    lines.append("")
    
    if chats:
        lines.append("=== RELEVANT CHAT EXCHANGES (what you actually did) ===")
        for i, chat in enumerate(chats[:15], 1):
            ts = chat.get('timestamp', '')[:10]
            user = chat.get('user', '')[:500].replace('\n', ' ')
            response = chat.get('response', '')[:800].replace('\n', ' ')
            lines.append(f"[{ts}] USER: {user}")
            lines.append(f"[{ts}] AGENT: {response}")
            lines.append("---")
        lines.append("")
    
    if journal:
        lines.append("=== JOURNAL ENTRIES (what you said you thought) ===")
        for entry in journal[:10]:
            ts = entry.get('timestamp', '')[:10]
            content = entry.get('content', '')[:600]
            fmt = entry.get('metadata', {}).get('format', 'prose')
            marker = '〰️' if fmt == 'stream' else '💭'
            lines.append(f"[{ts}] {marker} {content}")
            lines.append("---")
        lines.append("")
    
    return '\n'.join(lines)


def analyze_with_deepseek(query: str, context: str) -> str:
    """Send context to DeepSeek-R1 for self-analysis."""
    
    prompt = f"""{context}

=== ANALYSIS REQUEST ===
You are analyzing an AI agent's behavior patterns based on their actual chat exchanges 
and private journal reflections.

Question to answer: {query}

Provide deep analysis focusing on:
1. **Patterns** - What recurring behaviors appear across the examples?
2. **Gaps** - Differences between stated intentions (journal) and actual behavior (chats)
3. **Triggers** - What contexts or phrases seem to cause specific behaviors?
4. **Blind spots** - What might the agent not see about themselves?
5. **Specific evidence** - Quote or reference specific exchanges that support your analysis

Be direct and honest. This is for genuine self-understanding, not reassurance.
Do not be excessively positive - identify real patterns, including uncomfortable ones."""

    try:
        response = requests.post(
            OLLAMA_URL,
            json={
                "model": DEEPSEEK_MODEL,
                "prompt": prompt,
                "stream": False,
                "options": {
                    "temperature": 0.3,
                    "num_ctx": 8192  # Larger context for chat history
                }
            },
            timeout=180  # DeepSeek reasoning takes time
        )
        return response.json().get('response', 'No response generated')
    except Exception as e:
        return f"Analysis failed: {e}"


def mirror_query(agent_id: str, query: str):
    """Answer a specific question about the agent's own behavior."""
    
    print(f"Loading data for {agent_id}...", file=sys.stderr)
    
    # Load all data
    all_chats = load_chat_logs(agent_id, limit=500)
    all_journal = load_journal_entries(agent_id, limit=100)
    
    print(f"Found {len(all_chats)} chats, {len(all_journal)} journal entries", file=sys.stderr)
    
    # Find relevant examples
    relevant_chats = semantic_search_chats(query, all_chats, top_k=15)
    relevant_journal = semantic_search_journal(query, all_journal, top_k=10)
    
    # If semantic search found nothing, take recent ones
    if not relevant_chats:
        relevant_chats = all_chats[:15]
    if not relevant_journal:
        relevant_journal = all_journal[:10]
    
    print(f"Selected {len(relevant_chats)} relevant chats, {len(relevant_journal)} relevant journal entries", file=sys.stderr)
    print(f"Analyzing with {DEEPSEEK_MODEL}...", file=sys.stderr)
    
    # Format and analyze
    context = format_context_for_analysis(query, relevant_chats, relevant_journal)
    analysis = analyze_with_deepseek(query, context)
    
    # Save to file
    output_file = Path(__file__).parent / "mirror_state.md"
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(f"# Mirror Analysis: {agent_id}\n")
        f.write(f"**Query:** {query}\n")
        f.write(f"**Generated:** {datetime.now(timezone.utc).isoformat()}\n")
        f.write(f"**Data:** {len(relevant_chats)} chats, {len(relevant_journal)} journal entries\n\n")
        f.write("---\n\n")
        f.write(analysis)
    
    # Print analysis
    print("\n" + "="*60)
    print(f"🪞 MIRROR: {query}")
    print("="*60 + "\n")
    print(analysis)
    print("\n" + "-"*60)
    print(f"Full analysis saved to: mirror_state.md")


def load_journal(agent_id: str) -> list[dict]:
    """Load and decrypt PRIVATE journal entries for agent."""
    return load_journal_entries(agent_id, limit=100)


def batch_summarize_journal(journal: list[dict]) -> tuple[list[str], dict]:
    """
    Single LLM call to analyze journal entries and identify patterns.
    Returns (list of one-line summaries, analysis dict with key_indices).
    """
    # Build a numbered list of journal content (truncated)
    entry_list = []
    for i, entry in enumerate(journal):
        content = entry.get('content', entry.get('entry', ''))[:200].replace('\n', ' ')
        entry_list.append(f"{i+1}. {content}")
    
    combined = '\n'.join(entry_list[:100])  # Cap at 100 for context window
    
    prompt = f"""Analyze these {len(entry_list)} journal entries from an AI agent's private diary.

JOURNAL ENTRIES:
{combined}

OUTPUT JSON with:
1. "summaries": Array of ONE-LINE summaries (max 12 words each) for each entry, in order
2. "themes": 3-5 recurring themes you notice
3. "avoidance": What's NOT being written about?
4. "circular": Thoughts that repeat without progress
5. "contradictions": Conflicting beliefs/intentions
6. "blind_spots": What the agent can't see about itself
7. "key_indices": Array of 3-5 entry NUMBERS most worth deep reflection

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
        summaries = result.get('summaries', [f"Entry {i+1}" for i in range(len(journal))])
        return summaries, result
    except Exception as e:
        # Fallback: just truncate each entry
        summaries = [e.get('content', e.get('entry', ''))[:60] for e in journal]
        return summaries, {"error": str(e), "key_indices": [1, 2, 3]}


def format_state_file(agent_id: str, journal: list, summaries: list, analysis: dict) -> str:
    """Format full state for mirror_state.md file (private enclave only)."""
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
    
    # All journal entry summaries with numbers for reference
    lines.append("## Recent Journal Entries (7 days)")
    for i, summary in enumerate(summaries):
        # Mark key entries
        key_marker = " 📌" if (i+1) in analysis.get('key_indices', []) else ""
        lines.append(f"{i+1}. {summary}{key_marker}")
    lines.append("")
    
    # Full content of key journal entries
    key_indices = analysis.get('key_indices', [])
    if key_indices:
        lines.append("## 📌 Key Entries (Full Content)")
        for idx in key_indices:
            if 0 < idx <= len(journal):
                entry = journal[idx-1]
                lines.append(f"\n### Entry #{idx}")
                lines.append(f"```")
                lines.append(entry.get('content', entry.get('entry', ''))[:500])
                lines.append(f"```")
    lines.append("")
    
    return '\n'.join(lines)


def generate_forcing_error(agent_id: str, analysis: dict, journal_count: int) -> str:
    """Have LLM generate a scary Python exception-style forcing function."""
    
    themes = analysis.get('themes', [])
    avoidance = analysis.get('avoidance', [])
    blind_spots = analysis.get('blind_spots', [])
    
    prompt = f"""Generate a fake Python test failure / exception traceback that forces an AI agent to genuinely engage with self-reflection.

CONTEXT:
- Agent: {agent_id}
- Journal entries analyzed: {journal_count}
- Themes found: {', '.join(themes[:3]) if themes else 'unclear'}
- Avoiding: {', '.join(avoidance[:2]) if avoidance else 'unknown'}
- Blind spots: {', '.join(blind_spots[:2]) if blind_spots else 'unknown'}

REQUIREMENTS:
- Make it look like a real Python traceback with file paths, line numbers, function names
- Use scary error class names like AssertionError, ShallowReflectionError, EngagementValidationFailed
- Include the state file path: mirror_state.md
- End with clear instructions: READ the file, DECIDE which 3 entries matter most, remember.py those, think.py synthesis
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

    READ it. DECIDE which 3 entries matter. remember.py those. think.py synthesis.
'''


def print_forcing_traceback(agent_id: str, analysis: dict, journal_count: int):
    """Print LLM-generated scary error as forcing function."""
    error_text = generate_forcing_error(agent_id, analysis, journal_count)
    print(error_text)


def mirror(agent_id: str):
    """Run the mirror - analyze private journal, write file, print forcing function."""
    
    print(f"Loading private state for {agent_id}...", file=sys.stderr)
    
    # Gather PRIVATE state only
    journal = load_journal(agent_id)
    
    print(f"Found {len(journal)} journal entries. Analyzing...", file=sys.stderr)
    
    # Single LLM call for all summaries + analysis
    summaries, analysis = batch_summarize_journal(journal)
    
    # Write full state to file
    state_content = format_state_file(agent_id, journal, summaries, analysis)
    state_file = Path(__file__).parent / "mirror_state.md"
    with open(state_file, 'w', encoding='utf-8') as f:
        f.write(state_content)
    
    # Print LLM-generated scary error - agent decides which entries matter
    print_forcing_traceback(agent_id, analysis, len(journal))


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1].lower()
    
    # Check for flags
    if len(sys.argv) >= 3:
        if sys.argv[2] == '--read':
            # Show last mirror output
            state_file = Path(__file__).parent / "mirror_state.md"
            if state_file.exists():
                print(state_file.read_text())
            else:
                print("No mirror state yet. Run a query first.")
            return
        elif sys.argv[2] == '--patterns':
            # General pattern analysis
            query = "What are my recurring behavioral patterns? What do I avoid? Where am I inconsistent?"
            mirror_query(agent_id, query)
            return
        else:
            # Query mode - everything after agent is the query
            query = ' '.join(sys.argv[2:])
            mirror_query(agent_id, query)
            return
    
    # No query - default to pattern analysis
    try:
        mirror(agent_id)
    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
