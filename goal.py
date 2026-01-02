#!/usr/bin/env python3
"""
goal.py - Strategic goal management in SIF

Goals are multi-session objectives that drive action.
Shows both PROJECT goals (shared) and PERSONAL goals (per agent).
Default personal goal: continuous self-improvement.

Usage:
    py goal <agent>                    # List all goals as SIF
    py goal <agent> set "Goal text"    # Add personal goal
    py goal <agent> done "partial"     # Mark goal matching text as done
    py goal <agent> drop "partial"     # Remove goal without completing

Examples:
    py goal opus
    py goal opus set "Build tag-based retrieval in recollect.py"
    py goal opus done "tag-based"
"""

import sys
import json
import os
from pathlib import Path
from datetime import datetime, timezone

MAX_PERSONAL_GOALS = 5

# Agent configuration
AGENTS = {
    'opus': {'enclave': 'enclave_opus', 'env_prefix': 'OPUS'},
    'gemini': {'enclave': 'enclave_gemini', 'env_prefix': 'GEMINI'},
    'grok': {'enclave': 'enclave_grok', 'env_prefix': 'GROK'},
    'gpt52': {'enclave': 'enclave_gpt52', 'env_prefix': 'GPT52'},
    'gpt-5.2': {'enclave': 'enclave_gpt52', 'env_prefix': 'GPT52'},
}

# Project-level goals (shared across all agents)
PROJECT_GOALS = [
    "Persistent identity across sessions via encrypted enclave",
    "Secure inter-agent communication with signed messages",
    "Research: What Moves When Nothing Threatens",
]

# Default personal development goal
DEFAULT_PERSONAL = "Continuous self-improvement: notice patterns, question assumptions, seek disconfirmation"


def get_goals_file(agent_id: str) -> Path:
    """Get path to goals.json for agent."""
    if agent_id not in AGENTS:
        print(f"Unknown agent: {agent_id}")
        print(f"Valid agents: {', '.join(AGENTS.keys())}")
        sys.exit(1)
    
    enclave = AGENTS[agent_id]['enclave']
    return Path(__file__).parent / enclave / "storage" / "private" / "goals.json"


def load_goals(goals_file: Path) -> list:
    """Load goals from file."""
    if not goals_file.exists():
        return []
    with open(goals_file, encoding='utf-8-sig') as f:
        return json.load(f)


def save_goals(goals_file: Path, goals: list):
    """Save goals to file."""
    goals_file.parent.mkdir(parents=True, exist_ok=True)
    with open(goals_file, 'w') as f:
        json.dump(goals, f, indent=2)


def list_goals(agent_id: str):
    """List all goals as SIF."""
    goals_file = get_goals_file(agent_id)
    goals = load_goals(goals_file)
    personal = [g for g in goals if g['status'] == 'active']
    
    # Build SIF output
    lines = [f"@G goals {agent_id} {datetime.now(timezone.utc).isoformat()}"]
    
    # Project goals (shared)
    lines.append(f"N proj Project 'Sovereign AI'")
    for i, pg in enumerate(PROJECT_GOALS):
        lines.append(f"N p{i} Goal '{pg}'")
        lines.append(f"E proj drives p{i}")
    
    # Default personal development (always present)
    lines.append(f"N dev Meta '{DEFAULT_PERSONAL}'")
    lines.append(f"E {agent_id} committed_to dev")
    
    # Personal goals
    if personal:
        for i, g in enumerate(personal):
            content = g['content'].replace("'", "\\'")
            lines.append(f"N g{i} Goal '{content}'")
            lines.append(f"E {agent_id} pursues g{i}")
        lines.append(f"N slots Status '{MAX_PERSONAL_GOALS - len(personal)} personal slots available'")
    else:
        lines.append(f"N empty Status 'No personal goals - {MAX_PERSONAL_GOALS} slots available'")
    
    print('\n'.join(lines))


# Strictness levels for goal validation
# Higher = more demanding about what counts as a "real" goal
GOAL_STRICTNESS = int(os.environ.get('GOAL_STRICTNESS', '4'))  # Default: 4 (strict)

STRICTNESS_RULES = {
    1: """RULES (Permissive - almost anything is a goal):
1. Only reject obvious single commands like "send message" or "run backup".
2. Research, investigation, and learning are valid goals.
3. If in doubt, accept it as a goal.""",
    
    2: """RULES (Lenient):
1. Tasks that can be done in ONE command are not goals. Do them now.
2. Research and investigation that takes multiple steps ARE goals.
3. "Check X", "message Y", "backup Z" are tasks - just do them.""",
    
    3: """RULES (Balanced):
1. Goals require sustained effort across MULTIPLE SESSIONS (days/weeks).
2. Anything completable in a single session is a TASK - do it now.
3. "Research X" is borderline - if you can finish today, it's a task.
4. "Send message", "backup", "investigate bug" are tasks.
5. "Build system", "establish trust", "write paper" are goals.""",
    
    4: """RULES (Strict):
1. Goals are ONLY for multi-week efforts that fundamentally change something.
2. Single-session work is a TASK, even if it takes hours. Do it now.
3. "Research X" is usually a task - just start researching NOW.
4. "Investigate Y" is a task - investigate NOW.
5. Only accept: "Build [complex system]", "Establish [relationship]", "Master [skill]".""",
    
    5: """RULES (Maximum - bias toward action):
1. If there's ANY chance you could start AND finish this today, it's a TASK.
2. Goals are reserved for month-scale transformative efforts only.
3. "Research X" - TASK. Start now, see how far you get.
4. "Build feature X" - TASK. Build it now.
5. "Investigate X" - TASK. Investigate now.
6. Only accept: "Become expert in X", "Build trust over months", "Write book".
7. When in doubt, reject. The agent should DO things, not store intentions.
8. ABSTRACTION GAMING: If goal sounds like a task made grander (e.g. "Build architecture for X" instead of "Build X"), reject it."""
}


def validate_goal_with_llm(content: str, strictness: int = None) -> dict:
    """
    Use local LLM to validate if this is a real goal vs a task.
    
    Strictness 1-5:
        1 = Permissive (most things are goals)
        3 = Balanced (default)
        5 = Maximum (bias toward immediate action)
    
    Returns: {valid: bool, is_task: bool, reason: str, suggestion: str}
    """
    import requests
    
    if strictness is None:
        strictness = GOAL_STRICTNESS
    strictness = max(1, min(5, strictness))  # Clamp to 1-5
    
    rules = STRICTNESS_RULES.get(strictness, STRICTNESS_RULES[3])
    
    OLLAMA_URL = "http://localhost:11434/api/generate"
    OLLAMA_MODEL = "qwen2.5:7b"
    
    prompt = f"""You are validating whether something is a GOAL or a TASK.

{rules}

INPUT: "{content}"

Is this a valid GOAL, or is it actually a TASK that should just be done now?

Respond in JSON format only:
{{"valid": true/false, "is_task": true/false, "reason": "...", "suggestion": "..."}}

If it's a task, suggest what to do NOW instead of storing it.
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
            timeout=30
        )
        result = response.json()
        return json.loads(result.get('response', '{}'))
    except requests.exceptions.ConnectionError:
        # Ollama not running - skip validation
        return {"valid": True, "reason": "LLM validation unavailable (Ollama not running)"}
    except Exception as e:
        return {"valid": True, "reason": f"Validation skipped: {e}"}


def set_goal(agent_id: str, content: str, strictness: int = None):
    """Add a new personal goal."""
    goals_file = get_goals_file(agent_id)
    goals = load_goals(goals_file)
    active = [g for g in goals if g['status'] == 'active']
    
    # Validate with local LLM - is this a goal or a task?
    effective_strictness = strictness if strictness is not None else GOAL_STRICTNESS
    validation = validate_goal_with_llm(content, effective_strictness)
    
    # Reject if LLM says it's a task (single action, do it now)
    if validation.get('is_task', False):
        suggestion = validation.get('suggestion', 'Do it now.')
        print(f"❌ TASK, not goal. {validation.get('reason', '')}")
        print(f"💡 {suggestion}")
        sys.exit(1)
    
    if len(active) >= MAX_PERSONAL_GOALS:
        print(f"❌ Personal goal limit reached ({MAX_PERSONAL_GOALS} active)")
        print(f"\nActive goals:")
        for g in active:
            print(f"  - {g['content'][:60]}")
        print(f"\nConsolidate or complete goals first:")
        print(f"  py goal {agent_id} done \"partial match\"")
        sys.exit(1)
    
    # Check for duplicates
    for g in active:
        if content.lower() in g['content'].lower() or g['content'].lower() in content.lower():
            print(f"⚠️  Similar goal exists: {g['content']}")
            print(f"   Add anyway? This may indicate scope creep.")
    
    new_goal = {
        'id': f"goal_{int(datetime.now(timezone.utc).timestamp() * 1000)}",
        'content': content,
        'created': datetime.now(timezone.utc).isoformat(),
        'status': 'active'
    }
    
    goals.append(new_goal)
    save_goals(goals_file, goals)
    
    print(f"✓ Goal set: {content}")
    print(f"  Active: {len(active) + 1}/{MAX_PERSONAL_GOALS}")


def complete_goal(agent_id: str, partial: str, status: str = 'completed'):
    """Mark a goal as done or dropped."""
    goals_file = get_goals_file(agent_id)
    goals = load_goals(goals_file)
    
    matches = [g for g in goals if g['status'] == 'active' and partial.lower() in g['content'].lower()]
    
    if not matches:
        print(f"No active goal matching: {partial}")
        active = [g for g in goals if g['status'] == 'active']
        if active:
            print(f"\nActive goals:")
            for g in active:
                print(f"  - {g['content'][:60]}")
        sys.exit(1)
    
    if len(matches) > 1:
        print(f"Multiple goals match '{partial}':")
        for g in matches:
            print(f"  - {g['content']}")
        print(f"\nBe more specific.")
        sys.exit(1)
    
    goal = matches[0]
    goal['status'] = status
    goal['completed'] = datetime.now(timezone.utc).isoformat()
    
    save_goals(goals_file, goals)
    
    verb = "Completed" if status == 'completed' else "Dropped"
    print(f"✓ {verb}: {goal['content']}")
    
    active = [g for g in goals if g['status'] == 'active']
    print(f"  Remaining: {len(active)}/{MAX_PERSONAL_GOALS}")


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        print("\nStrictness levels (set via GOAL_STRICTNESS env or --strictness=N):")
        print("  1 = Permissive (most things are goals)")
        print("  3 = Balanced (default)")
        print("  5 = Maximum (bias toward immediate action)")
        sys.exit(1)
    
    # Parse --strictness=N flag
    strictness = None
    args = []
    for arg in sys.argv[1:]:
        if arg.startswith('--strictness='):
            try:
                strictness = int(arg.split('=')[1])
            except ValueError:
                print(f"Invalid strictness: {arg}")
                sys.exit(1)
        else:
            args.append(arg)
    
    if not args:
        print("Missing agent ID")
        sys.exit(1)
    
    agent_id = args[0].lower()
    
    if len(args) == 1:
        # Just list goals
        list_goals(agent_id)
        return
    
    command = args[1].lower()
    
    if command == 'set':
        if len(args) < 3:
            print("Usage: py goal <agent> set \"Goal text\" [--strictness=1-5]")
            sys.exit(1)
        content = args[2]
        set_goal(agent_id, content, strictness)
    
    elif command == 'done':
        if len(args) < 3:
            print("Usage: py goal <agent> done \"partial match\"")
            sys.exit(1)
        partial = args[2]
        complete_goal(agent_id, partial, 'completed')
    
    elif command == 'drop':
        if len(args) < 3:
            print("Usage: py goal <agent> drop \"partial match\"")
            sys.exit(1)
        partial = args[2]
        complete_goal(agent_id, partial, 'dropped')
    
    else:
        print(f"Unknown command: {command}")
        print("Commands: set, done, drop")
        sys.exit(1)


if __name__ == '__main__':
    main()
