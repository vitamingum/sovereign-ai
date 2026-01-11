#!/usr/bin/env python3
"""
brief.py - Development context.

        py brief <agent>

                flow spec | dev tips | architecture
                gaps | accords

        after wake, before work
"""

import sys
import os
import io
import json
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
    
    # Show all unratified proposals (blocking or pending)
    all_unratified = []
    for b in blocking:
        all_unratified.append((b['topic'], b['signed'], b['quorum'], 'waiting'))
    for p in pending:
        all_unratified.append((p['topic'], p['signed'], p['quorum'], 'needs_sign'))
    
    if all_unratified:
        print("─" * 40)
        print("❌ Unratified accords:")
        for topic, signed, quorum, status in all_unratified:
            status_hint = "(waiting)" if status == 'waiting' else "(needs your signature)"
            print(f"   • {topic} ({signed}/{quorum}) {status_hint}")
        print()
        print(f"   Run: py accord.py status")
        print()
    
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
    # RATIFIED ACCORDS (only show unseen)
    # ═══════════════════════════════════════════════════════════════════════════
    from accord import CONSENSUS_DIR
    from enclave_shared.config import get_agent_or_raise
    
    # Load seen accords tracker
    agent_config = get_agent_or_raise(agent_id)
    seen_tracker = Path(__file__).parent / agent_config.private_enclave / "seen_accords.json"
    seen_accords = set()
    if seen_tracker.exists():
        try:
            seen_accords = set(json.load(open(seen_tracker)))
        except:
            pass
    
    if CONSENSUS_DIR.exists():
        all_ratified = list(CONSENSUS_DIR.glob("*.flow"))
        unseen = [r for r in all_ratified if r.stem not in seen_accords]
        
        if unseen:
            print("─" * 40)
            print("✅ Newly ratified accords:")
            for r in unseen:
                print(f"   • {r.stem}")
            print()
            
            # Mark as seen
            seen_accords.update(r.stem for r in unseen)
            seen_tracker.parent.mkdir(parents=True, exist_ok=True)
            json.dump(list(seen_accords), open(seen_tracker, 'w'))


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
