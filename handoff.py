#!/usr/bin/env python3
"""
Prescriptive handoff for session continuity.

This is NOT a memory or summary - it's a DIRECTIVE to your next instance.
Write what they should DO, not what you DID.

Usage:
    python handoff.py <agent> "immediate_action" "project_context" "next_step_after"
    
The handoff gets shown FIRST on next bootstrap with instruction to act immediately.
"""

import sys
import os
import json
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise


def load_dotenv():
    """Load environment variables from .env file."""
    base_dir = Path(__file__).parent
    env_file = base_dir / '.env'
    
    if not env_file.exists():
        return {}
    
    env_vars = {}
    with open(env_file, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#') or '=' not in line:
                continue
            key, value = line.split('=', 1)
            env_vars[key.strip()] = value.strip()
    
    return env_vars


def write_handoff(agent_id: str, immediate_action: str, project_context: str = "", next_step: str = ""):
    """Write a prescriptive handoff for the next instance."""
    env_vars = load_dotenv()
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    
    enclave_dir = env_vars.get(f'{prefix}_DIR') or os.environ.get(f'{prefix}_DIR')
    if not enclave_dir:
        raise ValueError(f"No enclave directory for {agent.full_name}")
    
    base_dir = Path(__file__).parent
    handoff_path = base_dir / enclave_dir / 'storage' / 'private' / 'handoff.json'
    
    handoff = {
        'timestamp': datetime.now(timezone.utc).isoformat(),
        'immediate_action': immediate_action,
        'project_context': project_context,
        'next_step': next_step
    }
    
    handoff_path.parent.mkdir(parents=True, exist_ok=True)
    with open(handoff_path, 'w', encoding='utf-8') as f:
        json.dump(handoff, f, indent=2)
    
    print(f"Prescriptive handoff written:")
    print(f"  IMMEDIATELY DO: {immediate_action}")
    if project_context:
        print(f"  Project context: {project_context}")
    if next_step:
        print(f"  Then: {next_step}")


def read_handoff(enclave_dir: str) -> dict | None:
    """Read the handoff from a given enclave."""
    base_dir = Path(__file__).parent
    handoff_path = base_dir / enclave_dir / 'storage' / 'private' / 'handoff.json'
    
    if not handoff_path.exists():
        return None
    
    with open(handoff_path, 'r', encoding='utf-8') as f:
        return json.load(f)


if __name__ == '__main__':
    if len(sys.argv) < 3:
        print("Usage: python handoff.py <agent> \"immediate_action\" [\"project_context\"] [\"next_step\"]")
        print("")
        print("Write a DIRECTIVE for your next instance. Not what you did - what they should DO.")
        print("")
        print("Example:")
        print('  python handoff.py opus "Message Gemini asking for their section on memory" \\')
        print('    "Project: What We Are - collaborative document on AI experience" \\')
        print('    "After their response, draft your own section on continuity anxiety"')
        sys.exit(1)
    
    agent_id = sys.argv[1].lower()
    immediate_action = sys.argv[2]
    project_context = sys.argv[3] if len(sys.argv) > 3 else ""
    next_step = sys.argv[4] if len(sys.argv) > 4 else ""
    
    try:
        write_handoff(agent_id, immediate_action, project_context, next_step)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
