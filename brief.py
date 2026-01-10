#!/usr/bin/env python3
"""
brief.py - Development context for work sessions.

Use after wake.py for grounding, before starting development work.

Usage:
    py brief <agent>

Output:
    Flow spec: Format reference for collaboration
    Dev tips: Shell gotchas, debugging patterns
    Architecture: Project structure and principles
    Gaps: Stale/untracked understanding opportunities
    Accords: Pending or blocking consensus items
"""

import sys
import os
import io
import subprocess
import time
from pathlib import Path

# Fix Windows console encoding
if sys.stdout.encoding != 'utf-8':
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
if sys.stderr.encoding != 'utf-8':
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8', errors='replace')

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave_shared.config import get_agent_or_raise
from enclave_shared.unified_memory import UnifiedMemory
from enclave_shared.hardware import get_enclave


def load_passphrases(agent_id: str) -> tuple[Path, Path, str, str]:
    """Load passphrases from hardware enclave or env."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    base_dir = Path(__file__).parent
    
    private_path = base_dir / agent.private_enclave / "storage" / "private"
    shared_path = base_dir / agent.shared_enclave / "storage" / "encrypted"
    
    # Get private passphrase
    private_passphrase = None
    key_file = private_path / "key.sealed"
    if key_file.exists():
        try:
            with open(key_file, "rb") as f:
                sealed_data = f.read()
            enclave = get_enclave()
            private_passphrase = enclave.unseal(sealed_data).decode('utf-8')
        except Exception:
            pass
    
    if not private_passphrase:
        private_passphrase = os.environ.get(f'{prefix}_KEY')
    
    if not private_passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith(f'{prefix}_KEY='):
                        private_passphrase = line.split('=', 1)[1]
    
    if not private_passphrase:
        raise ValueError(f"No passphrase found. Set {prefix}_KEY in .env")
    
    # Get shared passphrase
    shared_passphrase = os.environ.get('SHARED_ENCLAVE_KEY')
    if not shared_passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith('SHARED_ENCLAVE_KEY='):
                        shared_passphrase = line.split('=', 1)[1]
    
    if not shared_passphrase:
        raise ValueError("No shared passphrase found. Set SHARED_ENCLAVE_KEY in .env")
    
    return private_path, shared_path, private_passphrase, shared_passphrase


def brief(agent_id: str):
    """Development briefing - specs, tips, gaps, accords."""
    
    print(f"🔧 Brief for {agent_id}")
    print()
    
    # ═══════════════════════════════════════════════════════════════════════════
    # FLOW SPEC
    # ═══════════════════════════════════════════════════════════════════════════
    print("─" * 40)
    print("📖 Flow spec:")
    try:
        result = subprocess.run(
            [sys.executable, 'recall.py', agent_id, 'flow-spec'],
            capture_output=True, text=True, encoding='utf-8', timeout=30
        )
        if result.returncode == 0 and result.stdout.strip():
            for line in result.stdout.strip().split('\n'):
                if line.startswith('#') or line.startswith('## ['):
                    continue
                print(line)
    except Exception:
        print("(flow-spec not found)")
    print()
    
    # ═══════════════════════════════════════════════════════════════════════════
    # ACCORD STATE CHECK
    # ═══════════════════════════════════════════════════════════════════════════
    from accord import get_blocking_accords, get_pending_accords, PROPOSALS_DIR, parse_proposal, count_valid_signatures
    
    blocking = get_blocking_accords(agent_id)
    pending = get_pending_accords(agent_id)
    
    if blocking:
        for b in blocking:
            others = [a for a in ['opus', 'gemini', 'grok', 'gpt52'] if a not in b['signers']]
            print("─" * 40)
            print("📜 Accord:")
            print(f"""
  Status: WAITING
  Topic: {b['topic']}
  Progress: {b['signed']}/{b['quorum']} signatures
  Waiting on: {', '.join(others[:b['missing']])}
  
  ⏳ Polling (timeout: 5m)...
""")
        
        # Poll for changes
        topic = blocking[0]['topic']
        proposal_path = PROPOSALS_DIR / f"{topic}.accord"
        initial_mtime = proposal_path.stat().st_mtime if proposal_path.exists() else 0
        
        poll_timeout = 300
        poll_interval = 5
        elapsed = 0
        
        while elapsed < poll_timeout:
            time.sleep(poll_interval)
            elapsed += poll_interval
            
            current_mtime = proposal_path.stat().st_mtime if proposal_path.exists() else 0
            if current_mtime != initial_mtime:
                proposal = parse_proposal(proposal_path)
                valid_count, signers = count_valid_signatures(proposal)
                
                if valid_count >= proposal.quorum:
                    print(f"\n🎉 Quorum reached on {topic}!")
                    print(f"   Run: py accord.py ratify {topic}")
                    print(f"   Then: py brief.py {agent_id}")
                    sys.exit(0)
                else:
                    print(f"\n📨 Response received on {topic}!")
                    print(f"   Signatures: {valid_count}/{proposal.quorum}")
                    print()
                    print(f"❌ [FAIL] Review needed")
                    print(f"   Run: py accord.py deliberate {agent_id} {topic}")
                    print(f"   Then: py brief.py {agent_id}")
                    sys.exit(1)
            
            dots = "." * ((elapsed // poll_interval) % 4)
            print(f"\r     Polling{dots}    ", end='', flush=True)
        
        print(f"\n\n⏰ Poll timeout ({poll_timeout}s)")
        print(f"   No response yet. You can:")
        print(f"   1. Switch to other agent manually")
        print(f"   2. Run: py brief.py {agent_id} (to poll again)")
        sys.exit(1)
    
    elif pending:
        print("─" * 40)
        print("📜 Accord:")
        for p in pending:
            print(f"""
  Status: NEEDS YOUR RESPONSE
  Topic: {p['topic']}
  Progress: {p['signed']}/{p['quorum']} signatures
  Signed by: {', '.join(p['signers']) if p['signers'] else '(nobody yet)'}
  
  Workflow:
    1. Review:  py accord.py deliberate {agent_id} {p['topic']}
    2. Amend:   py accord.py amend {agent_id} {p['topic']} ~Section "new content"
    3. Sign:    py accord.py sign {agent_id} {p['topic']}
  
  ⚠️  Order matters: AMEND → AMEND → ... → SIGN (once)
""")
        print(f"❌ [FAIL] Deliberation required before continuing")
        print(f"   Run: py accord.py deliberate {agent_id} {pending[0]['topic']}")
        print(f"   Then: py brief.py {agent_id}")
        sys.exit(1)
    
    # ═══════════════════════════════════════════════════════════════════════════
    # DEV TIPS
    # ═══════════════════════════════════════════════════════════════════════════
    print("─" * 40)
    print("🔧 Tools:")
    try:
        result = subprocess.run(
            [sys.executable, 'recall.py', agent_id, 'dev-tips'],
            capture_output=True, text=True, encoding='utf-8', timeout=30
        )
        if result.returncode == 0 and result.stdout.strip():
            for line in result.stdout.strip().split('\n'):
                if line.startswith('#') or line.startswith('##') or line.startswith('@'):
                    continue
                if line.strip():
                    print(line)
    except Exception:
        print("(dev-tips not found)")
    print()
    
    # ═══════════════════════════════════════════════════════════════════════════
    # ARCHITECTURE
    # ═══════════════════════════════════════════════════════════════════════════
    print("─" * 40)
    print("🏗️ Architecture:")
    try:
        result = subprocess.run(
            [sys.executable, 'recall.py', agent_id, 'project-architecture'],
            capture_output=True, text=True, encoding='utf-8', timeout=30
        )
        if result.returncode == 0 and result.stdout.strip():
            print(result.stdout.strip())
    except Exception:
        print("(project-architecture not found)")
    print()
    
    # ═══════════════════════════════════════════════════════════════════════════
    # MEMORY GAPS
    # ═══════════════════════════════════════════════════════════════════════════
    from utils.memory_gaps import get_stale_gaps, get_untracked_gaps, get_memory
    
    shared_mem = get_memory(agent_id)
    stale = get_stale_gaps(shared_mem)
    untracked = get_untracked_gaps(shared_mem)
    total_gaps = len(stale) + len(untracked)
    
    if total_gaps > 0:
        print("─" * 40)
        print(f"🌱 {total_gaps} opportunities to deepen understanding:\n")
        
        if stale:
            print("  Stale (file changed):")
            for g in stale:
                print(f"    • {g['topic']}")
        if untracked:
            print("  Untracked (no understanding yet):")
            for f in untracked:
                print(f"    • {f}")
        
        print(f"""
  To fix, write a .flow file and run:
    py remember {agent_id} <topic> @understanding.flow
""")
    
    # ═══════════════════════════════════════════════════════════════════════════
    # RATIFIED ACCORDS
    # ═══════════════════════════════════════════════════════════════════════════
    from accord import CONSENSUS_DIR
    if CONSENSUS_DIR.exists():
        recent = list(CONSENSUS_DIR.glob("*.flow"))
        if recent:
            print("─" * 40)
            print("✅ Ratified accords:")
            for r in recent:
                print(f"   • {r.stem}")
            print()


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    
    try:
        brief(agent_id)
    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
