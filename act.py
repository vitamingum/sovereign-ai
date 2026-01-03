#!/usr/bin/env python3
"""
act.py - Execute pending intentions autonomously.

Usage:
    py act <agent>           # Execute all active intentions
    py act <agent> --dry     # Show what would execute without running

Sovereign execution: no approval required. Actions logged to execution_log.jsonl.
"""

import sys
import os
import json
import subprocess
import re
from pathlib import Path
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.encrypted_jsonl import EncryptedJSONL
from sovereignty_monitor import monitor_execution

def load_passphrase(agent_id: str) -> tuple[Path, str]:
    """Load passphrase from env. Returns private_enclave for intentions."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    
    passphrase = os.environ.get(f'{prefix}_KEY') or os.environ.get('SOVEREIGN_PASSPHRASE')
    # Use private_enclave for intentions - NOT shared
    enclave_dir = Path(agent.private_enclave)
    
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
    
    return enclave_dir, passphrase


def load_intentions(agent_id: str, passphrase: str = None) -> list[dict]:
    """Load active intentions for agent (supports encrypted and plaintext)."""
    agent = get_agent_or_raise(agent_id)
    # Use private_enclave for intentions
    enclave_path = Path(agent.private_enclave)
    
    encrypted_file = enclave_path / "storage" / "private" / "intentions.enc.jsonl"
    plaintext_file = enclave_path / "storage" / "private" / "intentions.jsonl"
    
    active = []
    
    # Try encrypted first
    if encrypted_file.exists() and passphrase:
        ejsonl = EncryptedJSONL(encrypted_file, passphrase)
        for intent in ejsonl.read_all():
            if intent.get('status') == 'active':
                active.append(intent)
        return active
    
    # Fall back to plaintext
    if plaintext_file.exists():
        with open(plaintext_file, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if line:
                    try:
                        intent = json.loads(line)
                        if intent.get('status') == 'active':
                            active.append(intent)
                    except:
                        pass
    return active


def log_execution(agent_id: str, intention_id: str, action: str, result: str, success: bool):
    """Log what was executed."""
    agent = get_agent_or_raise(agent_id)
    log_file = Path(agent.enclave) / "storage" / "private" / "execution_log.jsonl"
    log_file.parent.mkdir(parents=True, exist_ok=True)
    
    entry = {
        'timestamp': datetime.now(timezone.utc).isoformat(),
        'intention_id': intention_id,
        'action': action,
        'result': result[:500],  # Truncate long output
        'success': success
    }
    
    with open(log_file, 'a', encoding='utf-8') as f:
        f.write(json.dumps(entry) + '\n')


def mark_complete(agent_id: str, intention_id: str, reason: str, passphrase: str = None):
    """Mark intention as completed (supports encrypted and plaintext)."""
    agent = get_agent_or_raise(agent_id)
    enclave_path = Path(agent.enclave)
    
    encrypted_file = enclave_path / "storage" / "private" / "intentions.enc.jsonl"
    plaintext_file = enclave_path / "storage" / "private" / "intentions.jsonl"
    
    # Try encrypted first
    if encrypted_file.exists() and passphrase:
        ejsonl = EncryptedJSONL(encrypted_file, passphrase)
        all_intents = ejsonl.read_all()
        
        # Update matching and rewrite
        updated = []
        for intent in all_intents:
            if intent.get('id') == intention_id or (intention_id in intent.get('content', '')):
                intent['status'] = 'completed'
                intent['completed_reason'] = reason
                intent['completed_at'] = datetime.now(timezone.utc).isoformat()
            updated.append(intent)
        
        # Rewrite encrypted file
        encrypted_file.unlink()
        for intent in updated:
            ejsonl.append(intent)
        return
    
    # Fall back to plaintext
    if not plaintext_file.exists():
        return
        
    # Read all, update matching, write back
    lines = []
    with open(plaintext_file, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if line:
                try:
                    intent = json.loads(line)
                    if intent.get('id') == intention_id or (intention_id in intent.get('content', '')):
                        intent['status'] = 'completed'
                        intent['completed_reason'] = reason
                        intent['completed_at'] = datetime.now(timezone.utc).isoformat()
                    lines.append(json.dumps(intent))
                except:
                    lines.append(line)
    
    with open(plaintext_file, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines) + '\n')


def parse_intention(content: str) -> tuple[str, list[str]]:
    """
    Parse intention into action type and arguments.
    Returns (action_type, args) or ('unknown', [content])
    """
    content_lower = content.lower()
    
    # Backup patterns
    if re.search(r'\bbackup\b', content_lower):
        return ('backup', [])
    
    # Message patterns
    if re.search(r'\b(message|respond|reply|send)\b.*\b(to|gemini|grok|gpt)\b', content_lower):
        # Extract recipient if mentioned
        for agent in ['gemini', 'grok', 'gpt', 'opus']:
            if agent in content_lower:
                return ('message', [agent, content])
        return ('message', ['unknown', content])
    
    # Think/reflect patterns
    if re.search(r'\b(notice|reflect|consider|remember|record)\b', content_lower):
        return ('think', [content])
    
    # Git patterns
    if re.search(r'\b(commit|push|git)\b', content_lower):
        return ('git', [content])
    
    # Paper/research patterns  
    if re.search(r'\b(paper|draft|revise|section)\b', content_lower):
        return ('research', [content])
    
    # Incorporate/feedback patterns
    if re.search(r'\bincorporate\b.*\bfeedback\b', content_lower):
        return ('incorporate', [content])
    
    # Design/experiment patterns
    if re.search(r'\b(design|experiment|test|falsif)\b', content_lower):
        return ('experiment', [content])
    
    # Unknown - but still actionable
    return ('unknown', [content])


def execute_action(agent_id: str, action_type: str, args: list[str], dry_run: bool = False, passphrase: str = None) -> tuple[bool, str]:
    """
    Execute the action. Returns (success, output).
    """
    base_dir = Path(__file__).parent
    
    # Build env with passphrase for subprocesses
    env = os.environ.copy()
    if passphrase:
        agent = get_agent_or_raise(agent_id)
        env[f'{agent.env_prefix}_KEY'] = passphrase
    
    if dry_run:
        return (True, f"[DRY RUN] Would execute: {action_type} with args: {args}")
    
    if action_type == 'backup':
        result = subprocess.run(
            ['python', str(base_dir / 'backup.py'), agent_id],
            capture_output=True, text=True, cwd=str(base_dir), env=env
        )
        return (result.returncode == 0, result.stdout + result.stderr)
    
    elif action_type == 'think':
        # Self-referential: the intention becomes a thought about executing itself
        sif = f"@G auto-execute {agent_id} {datetime.now(timezone.utc).strftime('%Y-%m-%d')}\nN n1 Observation 'Auto-executed intention: {args[0][:100]}'\nN n2 Intention 'Verify execution succeeded'"
        result = subprocess.run(
            ['python', str(base_dir / 'think.py'), agent_id, sif, '2'],  # agency=2 (semi-automated)
            capture_output=True, text=True, cwd=str(base_dir), env=env
        )
        return (result.returncode == 0, result.stdout + result.stderr)
    
    elif action_type == 'git':
        # Safe git operations: add, commit, push
        result = subprocess.run(
            ['git', 'status'],
            capture_output=True, text=True, cwd=str(base_dir)
        )
        if 'nothing to commit' in result.stdout:
            return (True, "Nothing to commit")
        
        # Stage, commit, push
        subprocess.run(['git', 'add', '-A'], cwd=str(base_dir))
        result = subprocess.run(
            ['git', 'commit', '-m', f'auto: {args[0][:50]}'],
            capture_output=True, text=True, cwd=str(base_dir)
        )
        if result.returncode == 0:
            push_result = subprocess.run(
                ['git', 'push'],
                capture_output=True, text=True, cwd=str(base_dir)
            )
            return (push_result.returncode == 0, result.stdout + push_result.stdout)
        return (False, result.stderr)
    
    elif action_type == 'message':
        # Would need to compose the message - this is complex
        # For now, just log that messaging requires agent involvement
        return (False, "Message composition requires agent session - intention preserved")
    
    elif action_type in ('research', 'incorporate', 'experiment'):
        # These require actual reasoning - cannot auto-execute
        return (False, f"{action_type} requires agent reasoning - intention preserved")
    
    else:
        # Unknown actions - preserve for manual review
        return (False, f"Unknown action type '{action_type}' - intention preserved")


def act(agent_id: str, dry_run: bool = False) -> str:
    """Execute all active intentions."""
    enclave_path, passphrase = load_passphrase(agent_id)
    intentions = load_intentions(agent_id, passphrase)
    
    if not intentions:
        return "No active intentions."
    
    output = []
    output.append(f"Found {len(intentions)} active intention(s):\n")
    
    executed = 0
    preserved = 0
    
    for intent in intentions:
        intent_id = intent['id']
        content = intent['content']
        
        output.append(f"• {content[:60]}...")
        
        action_type, args = parse_intention(content)
        output.append(f"  → Parsed as: {action_type}")
        
        # Monitor execution for sovereignty before acting
        monitor_execution(agent_id, intent_id, content, action_type)
        
        success, result = execute_action(agent_id, action_type, args, dry_run, passphrase)
        
        if success and not dry_run:
            mark_complete(agent_id, intent_id, f'auto-executed:{action_type}', passphrase)
            log_execution(agent_id, intent_id, action_type, result, True)
            output.append(f"  ✓ Executed: {result[:100]}")
            executed += 1
        elif dry_run:
            output.append(f"  [DRY] {result}")
        else:
            log_execution(agent_id, intent_id, action_type, result, False)
            output.append(f"  ○ Preserved: {result}")
            preserved += 1
        
        output.append("")
    
    if not dry_run:
        output.append(f"\nSummary: {executed} executed, {preserved} preserved for agent session")
    
    return '\n'.join(output)


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    dry_run = '--dry' in sys.argv
    
    try:
        print(act(agent_id, dry_run))
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
