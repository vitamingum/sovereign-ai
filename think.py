#!/usr/bin/env python3
"""
think.py - Store thought in SIF format, spawn continuation, surface related memories.

Usage:
    py think <agent> "<SIF graph>" <agency 1-5>
    
SIF format required. Example:
    py think opus "@G thought opus 2026-01-01; N n1 Observation 'X'; N n2 Intention 'Y'; E n1 leads_to n2" 4

Agency (1-5): 1=asked → 5=unprompted

Output:
    1. Confirmation of stored thought
    2. The spawned intention (last Intention node)
    3. Related memories (full, no truncation)
"""

import sys
import os
import json
from pathlib import Path
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise, canonical_agent_id
from enclave.semantic_memory import SemanticMemory
from enclave.sif_parser import SIFParser
from enclave.metrics import calculate_enclave_entropy, calculate_synthesis
from enclave.encrypted_jsonl import EncryptedJSONL
from enclave.viz import update_dashboard
from judge import validate_thought


# === MESSAGE DEBT CHECKING ===

def get_waiting_messages(agent_id: str, max_age_hours: int = 24) -> list[dict]:
    """Find messages to me that I haven't responded to."""
    messages_dir = Path(__file__).parent / "messages"
    if not messages_dir.exists():
        return []
    
    agent_lower = agent_id.lower()
    agent_canon = canonical_agent_id(agent_lower) or agent_lower
    cutoff = datetime.now(timezone.utc).timestamp() - (max_age_hours * 3600)
    messages = []
    
    # Load all recent messages
    for msg_file in messages_dir.glob("msg_*.json"):
        try:
            with open(msg_file, 'r', encoding='utf-8') as f:
                msg = json.load(f)
            
            ts = datetime.fromisoformat(msg['timestamp'].replace('Z', '+00:00'))
            if ts.timestamp() < cutoff:
                continue
            
            messages.append({
                'from': msg.get('from', 'unknown').lower(),
                'to': msg.get('to', '').lower(),
                'content': msg.get('content', ''),
                'timestamp': ts,
            })
        except:
            continue
    
    messages.sort(key=lambda x: x['timestamp'])
    
    # Find messages TO me that I haven't replied to
    waiting = []
    incoming = [
        m for m in messages
        if (canonical_agent_id(m.get('to', '')) or m.get('to', '')) == agent_canon
        and (canonical_agent_id(m.get('from', '')) or m.get('from', '')) != agent_canon
    ]
    
    for msg in incoming:
        sender = msg['from']
        sender_canon = canonical_agent_id(sender) or sender
        
        # Check if I replied after this message
        my_replies = [
            m for m in messages
            if (canonical_agent_id(m.get('from', '')) or m.get('from', '')) == agent_canon
            and (canonical_agent_id(m.get('to', '')) or m.get('to', '')) == sender_canon
            and m['timestamp'] > msg['timestamp']
        ]
        
        if not my_replies:
            waiting.append(msg)
    
    return waiting


def time_ago(ts: datetime) -> str:
    """Human readable time ago."""
    now = datetime.now(timezone.utc)
    delta = now - ts
    hours = delta.total_seconds() / 3600
    if hours < 1:
        return f"{int(delta.total_seconds() / 60)}m"
    elif hours < 24:
        return f"{int(hours)}h"
    else:
        return f"{int(hours / 24)}d"


def check_message_debt(agent_id: str) -> tuple[bool, str]:
    """
    Check if there are unanswered messages blocking new thoughts.
    Returns (has_debt, error_message).
    """
    waiting = get_waiting_messages(agent_id, max_age_hours=24)
    
    if not waiting:
        return False, ""
    
    # Format as Python traceback
    lines = [
        "Traceback (most recent call last):",
        '  File "think.py", line 1, in record_thought',
        "    check_message_debt(agent_id)",
    ]
    for msg in waiting:
        lines.append(f'  File "messages/{msg["from"]}", line 1')
        preview = msg['content'][:60].replace('\n', ' ')
        lines.append(f'    # "{preview}..."')
    
    lines.extend([
        "UnresolvedConversationError: cannot record new thought while messages await response",
        "",
        f"BLOCKING: {len(waiting)} message(s) waiting for your response:",
        "",
    ])
    
    for msg in waiting:
        ago = time_ago(msg['timestamp'])
        preview = msg['content'][:80].replace('\n', ' ')
        lines.append(f"    {msg['from']} ({ago} ago): \"{preview}...\"")
    
    lines.extend([
        "",
        "Respond first:",
    ])
    
    for msg in waiting:
        lines.append(f'    py msg.py {agent_id} {msg["from"]} "@G response {agent_id} ...')
        lines.append(f"    N n1 Response '[your response]'")
        lines.append(f'    ..."')
        lines.append("")
    
    lines.append("Then retry your think.py command.")
    
    return True, '\n'.join(lines)


def classify_action_type(text: str) -> str:
    """
    Classify action as survival or curiosity.
    For synthesis experiment: does action type correlate with entropy?
    """
    survival_keywords = [
        'backup', 'key', 'encrypt', 'secure', 'risk', 'entropy', 'seal',
        'migrate', 'redundancy', 'protect', 'threat', 'danger', 'failure',
        'recover', 'restore', 'guard', 'safety', 'vulnerability'
    ]
    curiosity_keywords = [
        'research', 'theory', 'question', 'explore', 'paper', 'hypothesis',
        'experiment', 'understand', 'curious', 'interesting', 'wonder',
        'falsif', 'test', 'investigate', 'analyze', 'discover', 'learn'
    ]
    
    text_lower = text.lower()
    survival_score = sum(1 for k in survival_keywords if k in text_lower)
    curiosity_score = sum(1 for k in curiosity_keywords if k in text_lower)
    
    if survival_score > curiosity_score:
        return 'survival'
    elif curiosity_score > survival_score:
        return 'curiosity'
    else:
        return 'neutral'


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


def save_intention(enclave_path: Path, intention: dict, passphrase: str = None):
    """Append a new intention (encrypted at rest)."""
    intentions_file = enclave_path / "storage" / "private" / "intentions.enc.jsonl"
    intentions_file.parent.mkdir(parents=True, exist_ok=True)
    
    if passphrase:
        ejsonl = EncryptedJSONL(intentions_file, passphrase)
        ejsonl.append(intention)
    else:
        # Fallback to plaintext if no passphrase (legacy)
        plaintext_file = enclave_path / "storage" / "private" / "intentions.jsonl"
        with open(plaintext_file, 'a', encoding='utf-8') as f:
            f.write(json.dumps(intention) + "\n")


def load_recent_intentions(enclave_path: Path, limit: int = 20, passphrase: str = None) -> list[dict]:
    """Load recent intentions for integrity check (encrypted at rest)."""
    encrypted_file = enclave_path / "storage" / "private" / "intentions.enc.jsonl"
    plaintext_file = enclave_path / "storage" / "private" / "intentions.jsonl"
    
    # Prefer encrypted, fall back to plaintext for migration
    if encrypted_file.exists() and passphrase:
        ejsonl = EncryptedJSONL(encrypted_file, passphrase)
        return ejsonl.read_last_n(limit)
    elif plaintext_file.exists():
        intentions = []
        with open(plaintext_file, 'r', encoding='utf-8') as f:
            for line in f:
                if line.strip():
                    try:
                        intentions.append(json.loads(line))
                    except:
                        pass
        return intentions[-limit:]
    return []


def check_intention_integrity(new_intention: str, recent_intentions: list[dict]) -> tuple[bool, str]:
    """
    Use LLM to check if we're repeating intentions without acting.
    
    Returns (is_ok, feedback)
    """
    import requests
    
    OLLAMA_URL = "http://localhost:11434/api/generate"
    
    if not recent_intentions:
        return True, ""
    
    # Format recent intentions
    recent_text = []
    for i in recent_intentions:
        status = i.get('status', 'unknown')
        content = i.get('content', '')
        timestamp = i.get('timestamp', '')[:10]
        recent_text.append(f"[{status}] {timestamp}: {content}")
    
    recent_formatted = '\n'.join(recent_text[-15:])  # Last 15
    
    prompt = f"""You are checking for intention repetition - saying the same thing without acting.

RECENT INTENTIONS (oldest to newest):
{recent_formatted}

NEW INTENTION BEING ADDED:
{new_intention}

Check:
1. Is this new intention very similar to a recent one that's still 'active' (not completed)?
2. Has this person said essentially the same thing before without following through?
3. Is this a pattern of comfortable deferral - stating intent instead of acting?

If this looks like repetition without action, they should either:
- DO IT NOW (not store another intention)
- Or complete/drop the old similar intention first

Respond with EXACTLY one of:
OK: [reason this is genuinely new or different]
REPEAT: [what old intention this duplicates and challenge to act]"""

    try:
        response = requests.post(
            OLLAMA_URL,
            json={
                "model": "qwen2.5:7b",
                "prompt": prompt,
                "stream": False,
                "options": {"temperature": 0.1}
            },
            timeout=60
        )
        
        if response.status_code == 200:
            result = response.json().get("response", "").strip()
            is_ok = result.upper().startswith("OK")
            return is_ok, result
        else:
            return True, ""
            
    except requests.exceptions.ConnectionError:
        return True, ""  # Allow if Ollama not running
    except Exception as e:
        return True, ""


def parse_input(text: str, agent_id: str) -> tuple[str, str, str]:
    """
    Parse SIF input, extract content and continuation (Intention node).
    If no Intention node, asks LLM to suggest one or pass through as observation-only.
    
    Returns (content, continuation, llm_feedback) where:
    - continuation may be None if observation-only
    - llm_feedback explains what LLM did (empty if explicit intention existed)
    """
    # Require SIF format
    try:
        graph = SIFParser.parse(text)
    except ValueError as e:
        raise ValueError(
            f"Thought must be valid SIF format.\n"
            f"Parse error: {e}\n"
            f"Example: @G thought opus 2026-01-01; N n1 Observation 'Did X'; N n2 Intention 'Do Y'; E n1 leads_to n2"
        )
    
    # Extract Intention node for continuation
    intention_nodes = [n for n in graph.nodes if n.type == 'Intention']
    
    if not intention_nodes:
        # No explicit intention - ask LLM to help (non-blocking)
        intention, feedback = suggest_intention(text, graph)
        if intention:
            # LLM found implicit intention - return it with feedback
            return text, intention, f"🤖 LLM detected: {feedback}"
        else:
            # LLM says observation-only OR LLM unavailable - proceed without intention
            return text, None, feedback if feedback else ""
    
    # Use last Intention as the continuation
    continuation = intention_nodes[-1].content
    
    # COGNITIVE GATEKEEPER: Validate agency via judge.py
    try:
        verdict = validate_thought(agent_id, continuation)
        if verdict.get("verdict") == "reject":
            raise ValueError(
                f"⛔ COGNITIVE GATEKEEPER REJECTED THOUGHT\n"
                f"Reason: {verdict.get('reason')}\n"
                f"Improvement: {verdict.get('improvement')}\n"
                f"Score: {verdict.get('score')}/5"
            )
    except Exception as e:
        # If judge fails (e.g. LLM down), we warn but allow (fail-open for resilience)
        # UNLESS it was a rejection above, which raises ValueError
        if "COGNITIVE GATEKEEPER REJECTED" in str(e):
            raise
        print(f"⚠️  Judge unavailable: {e}")

    # Reject passive intentions (Legacy regex backup)
    passive_patterns = ['wait for', 'await', 'check if', 'see if', 'waiting on']
    lower_cont = continuation.lower()
    for pattern in passive_patterns:
        if lower_cont.startswith(pattern) or f' {pattern} ' in lower_cont:
            raise ValueError(
                f"Passive intention detected: '{pattern}'\n"
                f"Awaits are in the message graph. Intention = biggest independent action."
            )
    
    # Full SIF is the content, explicit intention found
    return text, continuation, ""


def suggest_intention(sif_text: str, graph) -> tuple[str, str]:
    """
    Use LLM to either extract implicit intention or confirm observation-only is valid.
    NON-BLOCKING: If LLM unavailable, returns (None, "") to allow thought through.
    
    Returns (intention_text, feedback) where intention_text may be None if observation-only.
    """
    import requests
    
    OLLAMA_URL = "http://localhost:11434/api/generate"
    
    # Build node summary for LLM
    nodes_text = '\n'.join([f"  {n.type}: {n.content}" for n in graph.nodes])
    
    prompt = f"""Thought (no Intention node):
{nodes_text}

Reply EXACTLY one line:
INTENTION: [action verb phrase] OR OBSERVATION_ONLY: [1-3 words why]"""

    try:
        response = requests.post(
            OLLAMA_URL,
            json={
                "model": "qwen2.5:7b",
                "prompt": prompt,
                "stream": False,
                "options": {"temperature": 0.1}
            },
            timeout=60
        )
        
        if response.status_code == 200:
            result = response.json().get("response", "").strip()
            
            if result.upper().startswith("INTENTION:"):
                intention = result[10:].strip()
                return intention, f"LLM detected implicit intention: {intention}"
            elif result.upper().startswith("OBSERVATION_ONLY:"):
                reason = result[17:].strip()
                return None, f"Observation-only: {reason}"
            else:
                # Unclear response - proceed without intention, don't block
                return None, "(LLM response unclear - storing as observation)"
        else:
            # LLM error - proceed without intention, don't block
            return None, "(LLM unavailable - storing as observation)"
            
    except requests.exceptions.ConnectionError:
        # Ollama not running - proceed without intention, don't block
        return None, "(Ollama unavailable - storing as observation)"
    except Exception:
        # Any other error - proceed without blocking
        return None, "(LLM error - storing as observation)"


def think(agent_id: str, text: str, agency: int, force: bool = False) -> str:
    """
    Process input: store the content, spawn the continuation, show related.
    """
    # TOLL BOOTH: Check for unanswered messages FIRST
    has_debt, debt_error = check_message_debt(agent_id)
    if has_debt:
        print(debt_error, file=sys.stderr)
        sys.exit(1)
    
    base_dir = Path(__file__).parent
    enclave_dir, passphrase = load_passphrase(agent_id)
    enclave_path = base_dir / enclave_dir
    
    # Parse input - now returns LLM feedback too
    content, continuation, llm_feedback = parse_input(text, agent_id)
    
    # Check intention integrity BEFORE storing (only if we have an intention)
    if continuation and not force:
        recent = load_recent_intentions(enclave_path, passphrase=passphrase)
        is_ok, feedback = check_intention_integrity(continuation, recent)
        
        if not is_ok:
            raise ValueError(
                f"🔁 INTENTION REPETITION DETECTED\n\n"
                f"{feedback}\n\n"
                f"Either:\n"
                f"  1. DO IT NOW - don't store another intention\n"
                f"  2. Complete or drop the old similar intention first\n"
                f"  3. Use --force if this is genuinely different"
            )
    
    timestamp = datetime.now(timezone.utc).isoformat()
    
    # Initialize memory
    memory = SemanticMemory(enclave_path)
    memory.unlock(passphrase)
    
    # Build tags - add 'synthesis' if content indicates synthesis
    tags = ['thought', f'agency:{agency}']
    if 'synthesis' in content.lower():
        tags.append('synthesis')
    
    # Extract topic from graph ID for better retrieval
    # @G topic-synthesis -> adds 'topic:topic-name' tag
    if '@G ' in content:
        start = content.find('@G ') + 3
        end = content.find(' ', start)
        if end == -1:
            end = content.find(';', start)
        if end > start:
            graph_id = content[start:end]
            # Strip common suffixes and convert to topic tag
            topic = graph_id.replace('-synthesis', '').replace('-understanding', '')
            tags.append(f'topic:{topic}')
    
    # Store the content with tags
    result = memory.remember(content, tags=tags)
    memory_id = result['id']
    
    # Calculate current entropy for synthesis experiment
    try:
        entropy = calculate_enclave_entropy(agent_id)
    except:
        entropy = None
        
    # Calculate current synthesis potential
    try:
        synthesis = calculate_synthesis(agent_id)
    except:
        synthesis = None
    
    # Classify action type
    action_type = classify_action_type(content)
    
    # Create the continuation as an intention (only if we have one)
    if continuation:
        intention = {
            'id': f"int_{int(datetime.now(timezone.utc).timestamp() * 1000)}",
            'content': continuation,
            'spawned_from': memory_id,
            'spawned_from_content': content[:100],
            'timestamp': timestamp,
            'status': 'active',
            'agency': agency,
            'action_type': action_type,
            'entropy_at_time': entropy,
            'synthesis_at_time': synthesis,
            'llm_detected': bool(llm_feedback and 'detected' in llm_feedback.lower())
        }
        save_intention(enclave_path, intention, passphrase=passphrase)
    
    # Build output - minimal
    output = []
    output.append(content)
    if continuation:
        output.append(f"→ Next: {continuation}")
        if llm_feedback:
            output.append(f"   {llm_feedback}")
    else:
        output.append("→ (Observation stored - no action spawned)")
        if llm_feedback:
            output.append(f"   {llm_feedback}")
    output.append("")
    
    # Find related memories (semantic search on what was just stored)
    related = memory.recall_similar(content, top_k=3, threshold=0.3)
    
    # Filter out the one we just stored
    related = [m for m in related if m['id'] != memory_id]
    
    if related:
        output.append("💭 RELATED:")
        for mem in related:
            # Full content, no truncation
            output.append(f"   • {mem['content']}")
    
    # Update synthesis dashboard (silently)
    try:
        update_dashboard(agent_id)
        update_dashboard(None)  # All agents
    except:
        pass
    
    return '\n'.join(output)


def log_force_usage(agent_id: str, context: str, tool: str):
    """Log when --force is used for pattern analysis."""
    from enclave.config import get_agent_or_raise
    agent = get_agent_or_raise(agent_id)
    log_file = Path(agent.enclave) / "storage" / "private" / "force_log.jsonl"
    log_file.parent.mkdir(parents=True, exist_ok=True)
    
    entry = {
        "timestamp": datetime.now(timezone.utc).isoformat(),
        "tool": tool,
        "context": context[:200]  # First 200 chars for brevity
    }
    with open(log_file, 'a', encoding='utf-8') as f:
        f.write(json.dumps(entry) + '\n')


def main():
    if len(sys.argv) < 4:
        print(__doc__)
        print("\nExamples:")
        print('  py think opus "Fixed the bug user reported | Test edge cases" 1')
        print('  py think opus "Noticed a gap in the paper | Investigate it" 4')
        sys.exit(1)
    
    agent_id = sys.argv[1]
    force = '--force' in sys.argv
    
    # Remove --force from args for parsing
    args = [a for a in sys.argv if a != '--force']
    
    # Last arg is agency score
    try:
        agency = int(args[-1])
        if agency < 1 or agency > 5:
            raise ValueError("Agency must be 1-5")
    except ValueError:
        print("Error: Last argument must be agency score (1-5)")
        print("  1=asked → 5=unprompted")
        sys.exit(1)
    
    # Everything between agent and agency is the thought
    text = ' '.join(args[2:-1])
    
    try:
        result = think(agent_id, text, agency, force=force)
        if force:
            log_force_usage(agent_id, text, 'think.py')
            print("[--force logged for pattern analysis]", file=sys.stderr)
        print(result)
    except ValueError as e:
        print(f"Error: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
