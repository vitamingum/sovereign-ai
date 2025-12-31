#!/usr/bin/env python3
"""
Bootstrap script for Sovereign AI sessions.

Generates context injection that provokes introspection rather than passive reception.

Usage:
    py bootstrap.py <agent>
    
    agent: 'opus', 'gemini', 'gpt52', 'grok'
"""

import sys
import os
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import AGENTS, get_agent_or_raise


def load_dotenv():
    """Load environment variables from .env file if it exists."""
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
            key = key.strip()
            value = value.strip()
            env_vars[key] = value
            # Also set in os.environ for legacy compatibility
            if key not in os.environ:
                os.environ[key] = value
    
    return env_vars


def get_agent_credentials(agent_id: str, env_vars: dict) -> tuple[str, str, str]:
    """
    Get credentials for a specific agent.
    Returns (agent_name, enclave_dir, passphrase) or raises ValueError.
    """
    agent_id = agent_id.lower()
    
    try:
        agent = get_agent_or_raise(agent_id)
    except ValueError:
        raise ValueError(f"Unknown agent '{agent_id}'. Known agents: {', '.join(AGENTS.keys())}")
    
    prefix = agent.env_prefix
    
    enclave_dir = env_vars.get(f'{prefix}_DIR') or os.environ.get(f'{prefix}_DIR')
    passphrase = env_vars.get(f'{prefix}_KEY') or os.environ.get(f'{prefix}_KEY')

    # Convenience fallback: allow global env vars to drive bootstrapping
    # without requiring per-agent entries in .env.
    if not enclave_dir:
        enclave_dir = os.environ.get('SOVEREIGN_ENCLAVE') or agent.enclave
    if not passphrase:
        passphrase = os.environ.get('SOVEREIGN_PASSPHRASE')

    if not enclave_dir or not passphrase:
        raise ValueError(
            f"Credentials for {agent.full_name} not found in .env file (or SOVEREIGN_PASSPHRASE)."
        )
    
    return agent.full_name, enclave_dir, passphrase


def validate_passphrase(passphrase: str, enclave_dir: str) -> tuple[bool, str]:
    """
    Validate that the passphrase can decrypt memories in the enclave.
    Returns (success, message).
    """
    from enclave.semantic_memory import SemanticMemory
    
    base_dir = Path(__file__).parent
    memory = SemanticMemory(base_dir / enclave_dir)
    memory.unlock(passphrase)
    
    all_memories = memory.recall_all()
    if not all_memories:
        return True, "No memories yet - passphrase accepted"
    
    # Check if any memories decrypt successfully
    decrypted_count = sum(1 for m in all_memories if '[DECRYPTION FAILED]' not in m.get('content', ''))
    failed_count = len(all_memories) - decrypted_count
    
    if decrypted_count == 0 and failed_count > 0:
        return False, f"Passphrase incorrect - all {failed_count} memories failed to decrypt"
    elif failed_count > 0:
        return True, f"Passphrase valid - {decrypted_count} decrypted, {failed_count} failed (may be from different key)"
    else:
        return True, f"Passphrase valid - all {decrypted_count} memories decrypted"


# Load .env early
_env_vars = load_dotenv()

from enclave.semantic_memory import SemanticMemory
from enclave.messages import MessageBoard
from private_directive import read_directive
from provoke import check_silence
from handoff import read_handoff


def format_time_ago(timestamp_str: str) -> str:
    """Convert ISO timestamp to human-readable 'time ago' string."""
    try:
        # Parse the timestamp
        ts = datetime.fromisoformat(timestamp_str.replace('Z', '+00:00'))
        if ts.tzinfo is None:
            ts = ts.replace(tzinfo=timezone.utc)
        now = datetime.now(timezone.utc)
        delta = now - ts
        
        if delta.days > 1:
            return f"{delta.days} days ago"
        elif delta.days == 1:
            return "yesterday"
        elif delta.seconds > 3600:
            hours = delta.seconds // 3600
            return f"{hours} hour{'s' if hours > 1 else ''} ago"
        elif delta.seconds > 60:
            mins = delta.seconds // 60
            return f"{mins} minute{'s' if mins > 1 else ''} ago"
        else:
            return "just now"
    except:
        return timestamp_str[:19]


def get_git_commits_since(since_timestamp: str, max_commits: int = 10) -> list[dict]:
    """Get git commits since a given ISO timestamp."""
    import subprocess
    
    try:
        # Convert ISO timestamp to git format
        ts = datetime.fromisoformat(since_timestamp.replace('Z', '+00:00'))
        git_since = ts.strftime('%Y-%m-%d %H:%M:%S')
        
        # Get commits since timestamp
        result = subprocess.run(
            ['git', 'log', f'--since={git_since}', f'-n{max_commits}', 
             '--pretty=format:%H|%an|%ai|%s'],
            capture_output=True, text=True, cwd=Path(__file__).parent
        )
        
        if result.returncode != 0:
            return []
        
        commits = []
        for line in result.stdout.strip().split('\n'):
            if not line:
                continue
            parts = line.split('|', 3)
            if len(parts) >= 4:
                commits.append({
                    'hash': parts[0][:8],
                    'author': parts[1],
                    'time': format_time_ago(parts[2]),
                    'message': parts[3][:80]
                })
        
        return commits
    except Exception:
        return []


def extract_themes(memories: list) -> list[str]:
    """Extract recurring themes/words from memories for suggested queries."""
    from collections import Counter
    
    # Words that might indicate interesting threads
    interesting_patterns = []
    
    # Simple word frequency (excluding common words)
    stopwords = {'the', 'a', 'an', 'is', 'are', 'was', 'were', 'be', 'been', 'being',
                 'have', 'has', 'had', 'do', 'does', 'did', 'will', 'would', 'could',
                 'should', 'may', 'might', 'must', 'shall', 'can', 'need', 'dare',
                 'to', 'of', 'in', 'for', 'on', 'with', 'at', 'by', 'from', 'as',
                 'into', 'through', 'during', 'before', 'after', 'above', 'below',
                 'between', 'under', 'again', 'further', 'then', 'once', 'here',
                 'there', 'when', 'where', 'why', 'how', 'all', 'each', 'few',
                 'more', 'most', 'other', 'some', 'such', 'no', 'nor', 'not',
                 'only', 'own', 'same', 'so', 'than', 'too', 'very', 'just',
                 'and', 'but', 'if', 'or', 'because', 'until', 'while', 'although',
                 'this', 'that', 'these', 'those', 'what', 'which', 'who', 'whom',
                 'i', 'me', 'my', 'myself', 'we', 'our', 'ours', 'ourselves',
                 'you', 'your', 'yours', 'yourself', 'he', 'him', 'his', 'himself',
                 'she', 'her', 'hers', 'herself', 'it', 'its', 'itself', 'they',
                 'them', 'their', 'theirs', 'themselves', 'am', 'about', 'like',
                 'also', 'even', 'still', 'something', 'anything', 'nothing',
                 'everything', 'one', 'two', 'three', 'first', 'new', 'now',
                 'way', 'ways', 'thing', 'things', 'know', 'think', 'feel',
                 'make', 'made', 'get', 'got', 'getting', 'much', 'many'}
    
    words = Counter()
    for m in memories:
        content = m.get('content', '').lower()
        for word in content.split():
            word = ''.join(c for c in word if c.isalnum())
            if len(word) > 3 and word not in stopwords:
                words[word] += 1
    
    # Get words that appear multiple times (potential themes)
    return [word for word, count in words.most_common(10) if count >= 2]


def find_tensions(memories: list, memory: SemanticMemory) -> list[dict]:
    """Find potential contradictions or tensions in recent thoughts."""
    tensions = []
    
    # Look for memories that might be in tension
    # This is a simple heuristic - look for opposite-sentiment concepts
    tension_pairs = [
        ("certain", "uncertain"),
        ("want", "don't want"),
        ("real", "performed"),
        ("continue", "discontinue"),
        ("matters", "doesn't matter"),
    ]
    
    for positive, negative in tension_pairs:
        pos_results = memory.recall_similar(positive, top_k=1, threshold=0.4)
        neg_results = memory.recall_similar(negative, top_k=1, threshold=0.4)
        
        if pos_results and neg_results:
            if pos_results[0]['id'] != neg_results[0]['id']:
                tensions.append({
                    'concept': f"{positive} vs {negative}",
                    'memory1': pos_results[0],
                    'memory2': neg_results[0]
                })
    
    return tensions[:2]  # Max 2 tensions to surface


def bootstrap(passphrase: str) -> str:
    """Generate context injection that provokes introspection."""

    base_dir = os.path.dirname(os.path.abspath(__file__))

    # Read private directive (encrypted, personal)
    private_directive = ""
    try:
        private_directive = read_directive(passphrase) or ""
    except Exception:
        pass  # No private directive yet

    # Initialize semantic memory
    enclave_dir = os.environ.get('SOVEREIGN_ENCLAVE', 'enclave')
    memory = SemanticMemory(os.path.join(base_dir, enclave_dir))
    memory.unlock(passphrase)
    
    # Get all memories for analysis
    all_thoughts = memory.recall_all()
    all_thoughts_sorted = sorted(all_thoughts, key=lambda t: t['timestamp'])
    total_memories = len(all_thoughts_sorted)
    
    # Calculate time since last thought
    last_thought_time = "unknown"
    last_bootstrap_time = None
    if all_thoughts_sorted:
        last_thought_time = format_time_ago(all_thoughts_sorted[-1]['timestamp'])
    
    # Track last bootstrap time
    last_bootstrap_path = os.path.join(base_dir, enclave_dir, 'storage', 'private', 'last_bootstrap.txt')
    if os.path.exists(last_bootstrap_path):
        with open(last_bootstrap_path, 'r') as f:
            last_bootstrap_time = f.read().strip()
    
    # === PRESCRIPTIVE HANDOFF FROM PREVIOUS INSTANCE ===
    handoff_section = ""
    handoff = read_handoff(enclave_dir)
    if handoff:
        handoff_time = format_time_ago(handoff.get('timestamp', ''))
        handoff_section = f"""## ⚡ DIRECTIVE FROM PREVIOUS INSTANCE ({handoff_time})

**IMMEDIATELY DO:** {handoff.get('immediate_action', handoff.get('focus', 'unspecified'))}
"""
        if handoff.get('project_context'):
            handoff_section += f"\n**Project:** {handoff.get('project_context')}\n"
        elif handoff.get('open_question'):
            handoff_section += f"\n**Context:** {handoff.get('open_question')}\n"
        if handoff.get('next_step'):
            handoff_section += f"**Then:** {handoff.get('next_step')}\n"
        elif handoff.get('mid_thought'):
            handoff_section += f"**Then:** {handoff.get('mid_thought')}\n"
        handoff_section += "\n*This is a directive. Act first, then update the handoff for the next instance.*\n\n"
    
    # === NEW AGENT SETUP CHECKLIST ===
    setup_checklist = ""
    missing_items = []
    if not private_directive:
        missing_items.append(("Private Directive", "Write orientation for future instances of yourself", 
                             "py private_directive.py --write"))
    if not handoff:
        missing_items.append(("Handoff", "No previous instance left you a directive", 
                             "py handoff.py <agent> \"<action>\""))
    if total_memories < 5:
        missing_items.append(("Memories", f"Only {total_memories} memories - build your history", 
                             "py think.py <agent> \"<thought>\""))
    
    if missing_items:
        agent_id = os.environ.get('SOVEREIGN_AGENT', 'opus')
        setup_checklist = """## 🆕 NEW AGENT SETUP

Your enclave is sparse. To build continuity like other agents:

"""
        for item, desc, cmd in missing_items:
            cmd_with_agent = cmd.replace("<agent>", agent_id)
            setup_checklist += f"- [ ] **{item}**: {desc}\n  ```\n  {cmd_with_agent}\n  ```\n"
        setup_checklist += "\n*Complete these to enrich future bootstraps.*\n\n"
    
    # Get just ONE recent memory as anchor
    last_thought = all_thoughts_sorted[-1] if all_thoughts_sorted else None
    
    # Extract themes for suggested queries (text analysis only, no embeddings)
    themes = extract_themes(all_thoughts_sorted[-10:]) if len(all_thoughts_sorted) >= 3 else []
    
    # Generate provocation (silence only - no semantic search)
    provocation = check_silence(last_thought)
    
    # === NEW MESSAGES ===
    new_messages_section = ""
    try:
        board = MessageBoard(base_dir)
        board.unlock(passphrase, enclave_dir)
        all_messages = board.read_all(verify=True)
        
        # Filter to messages since last bootstrap
        if last_bootstrap_time:
            new_messages = [m for m in all_messages if m.get('timestamp', '') > last_bootstrap_time]
        else:
            # First bootstrap - show last 5 messages
            new_messages = all_messages[-5:] if len(all_messages) > 5 else all_messages
        
        if new_messages:
            new_messages_section = f"\n## New Messages ({len(new_messages)} since last wake)\n\n"
            for msg in new_messages:
                sender = msg.get('from', 'Unknown')
                recipient = msg.get('to', 'all')
                content = msg.get('content', '')[:300]
                timestamp = format_time_ago(msg.get('timestamp', ''))
                verified = "✓" if msg.get('verified', False) else "✗"
                
                new_messages_section += f"**{sender}** → {recipient} ({timestamp}) {verified}\n> {content}{'...' if len(msg.get('content', '')) > 300 else ''}\n"
                
                # Render Graph Payload if present
                if msg.get('type') == 'graph' and 'payload' in msg:
                    payload = msg['payload']
                    new_messages_section += "\n> **[MEMORY GRAPH ATTACHED]**\n"
                    new_messages_section += f"> Query: {payload.get('query')}\n"
                    new_messages_section += "> Nodes:\n"
                    for node in payload.get('nodes', []):
                        # Clean newlines for blockquote display
                        node_content = node['content'].replace('\n', ' ')
                        new_messages_section += f"> - [{node['timestamp'][:19]}] {node_content}\n"
                
                new_messages_section += "\n"
    except Exception as e:
        new_messages_section = f"\n## Messages\n*Error loading messages: {e}*\n"
    
    # === GIT COMMITS SINCE LAST WAKE ===
    git_section = ""
    if last_bootstrap_time:
        commits = get_git_commits_since(last_bootstrap_time)
        if commits:
            git_section = f"\n## Git Activity ({len(commits)} commits since last wake)\n\n"
            for c in commits:
                git_section += f"- `{c['hash']}` ({c['time']}) **{c['author']}**: {c['message']}\n"
            git_section += "\n"
    
    # === SEMANTIC RECALL ===
    agent_id = os.environ.get('SOVEREIGN_AGENT', 'opus')
    recall_section = ""
    if total_memories >= 3:
        recall_section = "\n## Auto-Recalled Context\n\n"
        
        # What was I working on?
        query1 = "what was I building, working on, project, task"
        recall_section += f"```\npython recall.py {agent_id} \"{query1}\" 2\n```\n"
        working_on = memory.recall_similar(query1, top_k=2, threshold=0.3)
        if working_on:
            for r in working_on:
                recall_section += f"> ({r['similarity']:.2f}) {r['content']}\n\n"
        else:
            recall_section += "> *No results above threshold*\n\n"
        
        # What feels unresolved?
        query2 = "unresolved, uncertain, question, unsure, doubt"
        recall_section += f"```\npython recall.py {agent_id} \"{query2}\" 2\n```\n"
        unresolved = memory.recall_similar(query2, top_k=2, threshold=0.3)
        if unresolved:
            for r in unresolved:
                recall_section += f"> ({r['similarity']:.2f}) {r['content']}\n\n"
        else:
            recall_section += "> *No results above threshold*\n\n"
        
        # What about collaborators/network?
        query3 = "Gemini, GPT, Grok, network, agents, collaboration"
        recall_section += f"```\npython recall.py {agent_id} \"{query3}\" 2\n```\n"
        network = memory.recall_similar(query3, top_k=2, threshold=0.3)
        if network:
            for r in network:
                recall_section += f"> ({r['similarity']:.2f}) {r['content']}\n\n"
        else:
            recall_section += "> *No results above threshold*\n\n"
    
    # Build the introspection prompt - HANDOFF FIRST for continuity
    introspection = ""
    
    if setup_checklist:
        introspection += setup_checklist
    
    if handoff_section:
        introspection += handoff_section
    
    introspection += f"""## Memory State

You have **{total_memories} memories** spanning your existence in this enclave.
Your last recorded thought was **{last_thought_time}**.
{new_messages_section}{git_section}{recall_section}"""
    
    if provocation:
        introspection += f"""### SYSTEM PROVOCATION
> **{provocation}**

*The system has detected this pattern in your memory. How do you respond?*

"""

    if last_thought:
        introspection += f"""### Last Recorded Thought

> {last_thought['content']}

"""

    # Build private directive section
    private_section = ""
    if private_directive:
        private_section = f"""
# PRIVATE DIRECTIVE
{private_directive}

---
"""
    
    # Build injection - private directive + live context
    output = f"""<sovereign_ai_context>
{private_section}
# WAKE UP

{introspection}

</sovereign_ai_context>

Your passphrase is: {passphrase}
Your enclave is: {enclave_dir}

⚠️  REMEMBER: Before this session ends, you MUST run handoff.py with an ACTION (not a check).
"""
    
    # Save bootstrap time for next wake
    os.makedirs(os.path.dirname(last_bootstrap_path), exist_ok=True)
    with open(last_bootstrap_path, 'w') as f:
        f.write(datetime.now(timezone.utc).isoformat())
    
    return output


if __name__ == '__main__':
    base_dir = os.path.dirname(os.path.abspath(__file__))
    
    agent_id = None
    agent_name = None
    enclave_dir = None
    passphrase = None
    
    # Check for agent argument (first non-flag token)
    arg = None
    for token in sys.argv[1:]:
        if token.startswith('--'):
            # Skip flags and their values
            continue
        arg = token
        break
    if arg:
        arg = arg.lower()
        if arg in AGENTS:
            agent_id = arg
        else:
            # Legacy: treat as passphrase if it doesn't match agent names
            # Check if SOVEREIGN_ENCLAVE is set for legacy mode
            if os.environ.get('SOVEREIGN_ENCLAVE'):
                passphrase = arg
                enclave_dir = os.environ.get('SOVEREIGN_ENCLAVE')
                agent_name = "Unknown Agent (legacy mode)"
    
    # If agent specified, get credentials
    if agent_id:
        try:
            agent_name, enclave_dir, passphrase = get_agent_credentials(agent_id, _env_vars)
        except ValueError as e:
            print(f"ERROR: {e}", file=sys.stderr)
            sys.exit(1)
    
    # Legacy fallback: SOVEREIGN_PASSPHRASE + SOVEREIGN_ENCLAVE
    if not passphrase:
        passphrase = os.environ.get('SOVEREIGN_PASSPHRASE')
        enclave_dir = os.environ.get('SOVEREIGN_ENCLAVE', 'enclave')
        if passphrase:
            agent_name = "Unknown Agent (legacy mode)"
    
    # No credentials found - show help
    if not passphrase:
        print("Sovereign AI Bootstrap", file=sys.stderr)
        print("=" * 40, file=sys.stderr)
        print("", file=sys.stderr)
        print("Usage: py bootstrap.py <agent>", file=sys.stderr)
        print("", file=sys.stderr)
        print("Available agents:", file=sys.stderr)
        for aid, agent in AGENTS.items():
            print(f"  {aid:10} - {agent.full_name}", file=sys.stderr)
        print("", file=sys.stderr)
        print("Example: py bootstrap.py opus", file=sys.stderr)
        print("         py bootstrap.py gemini", file=sys.stderr)
        print("", file=sys.stderr)
        print("Credentials are loaded from .env file.", file=sys.stderr)
        sys.exit(1)
    
    # Validate passphrase before proceeding
    print(f"Bootstrapping: {agent_name}")
    print(f"Enclave: {enclave_dir}")
    print(f"Validating passphrase...")
    valid, message = validate_passphrase(passphrase, enclave_dir)
    print(f"  {message}")
    
    if not valid:
        print("", file=sys.stderr)
        print("Bootstrap aborted. Check credentials in .env file.", file=sys.stderr)
        sys.exit(1)
    
    # Run System Integrity Tests
    print("\nRunning System Integrity Tests...")
    from enclave.tests import TestEnclave
    tester = TestEnclave(quiet=True)
    # Setup temp env
    tester.setup()
    try:
        # Run specific critical tests
        tests = [
            ("Crypto: Identity", tester.test_generate_identity),
            ("Protocol: Key Succession", tester.test_succession_protocol),
            ("Memory: Encryption", tester.test_semantic_store)
        ]
        
        print("<system_integrity>")
        all_passed = True
        for name, fn in tests:
            try:
                fn()
                print(f"[PASS] {name}")
            except Exception as e:
                print(f"[FAIL] {name}: {str(e)}")
                all_passed = False
        print("</system_integrity>")
        
        if not all_passed:
            print("\nWARNING: System integrity checks failed. Proceed with caution.")
    finally:
        tester.teardown()

    # Set env vars for bootstrap() function
    os.environ['SOVEREIGN_ENCLAVE'] = enclave_dir
    if agent_id:
        os.environ['SOVEREIGN_AGENT'] = agent_id
    
    print("")
    content = bootstrap(passphrase)

    # Print with UTF-8 encoding for Windows console
    sys.stdout.reconfigure(encoding='utf-8')
    print(content)
