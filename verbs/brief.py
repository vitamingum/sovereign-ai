#!/usr/bin/env python3
"""
brief_v3.py - Development context (JIT + Grid).

    source: brief-understanding.flow
    compiler: Sovereign/Resident JIT
    infrastructure: SovereignAgent (The Grid)

    orient before working
        flow spec | dev tips | architecture
        gaps | accords

                        間委 → 間主
"""

import sys
import os
import json
import subprocess
from pathlib import Path

# Ensure project root in path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from lib_enclave.sovereign_agent import SovereignAgent

# We will try to import helper logic if available, or gracefull fail
try:
    from accord import get_blocking_accords, get_pending_accords, CONSENSUS_DIR
except ImportError:
    get_blocking_accords = None

def get_topic_content(mem, topic):
    """Fetch most recent understanding of a topic from memory."""
    try:
        # We want sys_understanding
        # We can't easily query by metadata with simple filter in current UnifiedMemory
        # so we filter type and scan.
        results = mem.filter(mem_type='sys_understanding', limit=200) # Optimization limit
        
        candidates = []
        for r in results:
            if r.get('metadata', {}).get('topic') == topic:
                candidates.append(r)
        
        if not candidates:
            return None
            
        # Sort by stored_at
        candidates.sort(key=lambda x: x.get('metadata', {}).get('stored_at', ''), reverse=True)
        return candidates[0].get('content', '')
        
    except Exception:
        return None

def show_section(title, content):
    if content:
        print("─" * 40)
        print(f"📖 {title}:")
        # Filter out comments unless verbose? No, showing everything is fine for brief.
        # Actually, brief implies "brief". Maybe just the summary lines?
        # The existing tool invokes recall which dumps the whole thing.
        # Let's clean it up slightly to just show non-comment lines if it's code?
        # No, let's trust the content.
        for line in content.splitlines():
             if line.startswith('## ['): continue
             print(line)
        print()

def main():
    agent_id = None
    if len(sys.argv) > 1:
        agent_id = sys.argv[1]
    
    # Sovereign Initialization (Auth-Once)
    try:
        sov = SovereignAgent.resolve(agent_id)
        agent_id = sov.agent.id
    except ValueError:
        print(__doc__)
        print("\nError: No active session. Specify agent or run 'py wake <agent>'")
        sys.exit(1)

    mem = sov.memory
    
    print(f"🔧 Brief for {agent_id}\n")
    
    # 1. FLOW SPEC
    flow_spec = get_topic_content(mem, 'flow-spec')
    if flow_spec:
        show_section("Flow Spec", flow_spec)
    else:
        print("(flow-spec not found in memory)")
        
    # 2. ACCORDS (if available)
    if get_blocking_accords:
        try:
            blocking = get_blocking_accords(agent_id)
            pending = get_pending_accords(agent_id)
            
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
                print("\n   Run: py accord.py status\n")
        except Exception as e:
            # accord.py might not be updated to grid yet, might fail on keys
            print(f"(Accord check skipped: {e})")
    
    # 3. WAYS
    ways = get_topic_content(mem, 'ways')
    if ways:
        show_section("Ways", ways)
        print("        py recall opus ways")
        print("        py remember opus \"@ways.flow\"")
        print("\n        間委 → 間主\n")
        
    # 4. ARCHITECTURE
    arch = get_topic_content(mem, 'project-architecture')
    if arch:
        show_section("Architecture", arch)
        
    # 5. GAPS
    # We can try to reuse utils.memory_gaps if compatible
    # But for v3, let's keep it simple or reimplement light version.
    # The utils module might need refactoring too.
    # For now, we will skip complex gap analysis to avoid breaking on legacy dependencies
    # unless we migrate utils.
    
    # 6. RATIFIED ACCORDS (New)
    # This relied on a file tracker in the enclave.
    # Using SovereignAgent, we know where the enclave is.
    try:
        seen_tracker = sov.base_dir / sov.agent.private_enclave / "seen_accords.json"
        seen_accords = set()
        if seen_tracker.exists():
             seen_accords = set(json.load(open(seen_tracker)))
             
        if get_blocking_accords and CONSENSUS_DIR.exists():
             all_ratified = list(CONSENSUS_DIR.glob("*.flow"))
             unseen = [r for r in all_ratified if r.stem not in seen_accords]
             
             if unseen:
                 print("─" * 40)
                 print("✅ Newly ratified accords:")
                 for r in unseen:
                     print(f"   • {r.stem}")
                 print()
                 
                 # Update tracker
                 seen_accords.update(r.stem for r in unseen)
                 with open(seen_tracker, 'w') as f:
                     json.dump(list(seen_accords), f)
    except Exception:
        pass

if __name__ == "__main__":
    main()

