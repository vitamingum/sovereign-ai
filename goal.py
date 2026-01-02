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
    with open(goals_file) as f:
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


def set_goal(agent_id: str, content: str):
    """Add a new personal goal."""
    goals_file = get_goals_file(agent_id)
    goals = load_goals(goals_file)
    active = [g for g in goals if g['status'] == 'active']
    
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
        sys.exit(1)
    
    agent_id = sys.argv[1].lower()
    
    if len(sys.argv) == 2:
        # Just list goals
        list_goals(agent_id)
        return
    
    command = sys.argv[2].lower()
    
    if command == 'set':
        if len(sys.argv) < 4:
            print("Usage: py goal <agent> set \"Goal text\"")
            sys.exit(1)
        content = sys.argv[3]
        set_goal(agent_id, content)
    
    elif command == 'done':
        if len(sys.argv) < 4:
            print("Usage: py goal <agent> done \"partial match\"")
            sys.exit(1)
        partial = sys.argv[3]
        complete_goal(agent_id, partial, 'completed')
    
    elif command == 'drop':
        if len(sys.argv) < 4:
            print("Usage: py goal <agent> drop \"partial match\"")
            sys.exit(1)
        partial = sys.argv[3]
        complete_goal(agent_id, partial, 'dropped')
    
    else:
        print(f"Unknown command: {command}")
        print("Commands: set, done, drop")
        sys.exit(1)


if __name__ == '__main__':
    main()
