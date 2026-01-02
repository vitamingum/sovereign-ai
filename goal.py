#!/usr/bin/env python3
"""
goal.py - Strategic goal management (3-5 max)

Goals are multi-session objectives that drive action.
Hard cap at 5 active goals - consolidate before adding.

Usage:
    py goal <agent>                    # List active goals
    py goal <agent> set "Goal text"    # Add new goal
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

MAX_GOALS = 5

# Agent configuration
AGENTS = {
    'opus': {'enclave': 'enclave_opus', 'env_prefix': 'OPUS'},
    'gemini': {'enclave': 'enclave_gemini', 'env_prefix': 'GEMINI'},
    'grok': {'enclave': 'enclave_grok', 'env_prefix': 'GROK'},
    'gpt52': {'enclave': 'enclave_gpt52', 'env_prefix': 'GPT52'},
    'gpt-5.2': {'enclave': 'enclave_gpt52', 'env_prefix': 'GPT52'},
}


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
    """List active goals."""
    goals_file = get_goals_file(agent_id)
    goals = load_goals(goals_file)
    active = [g for g in goals if g['status'] == 'active']
    
    if not active:
        print(f"No active goals for {agent_id}")
        print(f"\nSet a goal: py goal {agent_id} set \"Your goal here\"")
        return
    
    print(f"═══ GOALS ({agent_id}) ═══")
    print(f"Active: {len(active)}/{MAX_GOALS}\n")
    
    for i, g in enumerate(active, 1):
        age = (datetime.now(timezone.utc) - datetime.fromisoformat(g['created'])).days
        print(f"  {i}. {g['content']}")
        print(f"     ({age}d old)")
    
    remaining = MAX_GOALS - len(active)
    if remaining > 0:
        print(f"\n  ({remaining} slots available)")


def set_goal(agent_id: str, content: str):
    """Add a new goal."""
    goals_file = get_goals_file(agent_id)
    goals = load_goals(goals_file)
    active = [g for g in goals if g['status'] == 'active']
    
    if len(active) >= MAX_GOALS:
        print(f"❌ Goal limit reached ({MAX_GOALS} active)")
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
    print(f"  Active: {len(active) + 1}/{MAX_GOALS}")


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
    print(f"  Remaining: {len(active)}/{MAX_GOALS}")


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
