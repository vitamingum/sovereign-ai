#!/usr/bin/env python3
"""
watch.py - sentinel > observe  autonomy

    source: data/watch.flow
    context: data/sovereign.flow
    compiler: gemini (manual)
    date: 2026-01-14

intent
  monitor signal (messages)
  monitor time (schedule)
  trigger wake (action)
"""

import sys
import time
import argparse
import subprocess
from pathlib import Path

# Context: sovereign.flow -> environment.libs
sys.path.insert(0, str(Path(__file__).parent))

from enclave_shared.sovereign_agent import SovereignAgent
from enclave_shared import transport

def wake(agent_id, reason, with_messages=False):
    """Trigger the wake cycle."""
    print(f"\n[watch] Trigger: {reason}")
    print(f"[watch] Waking {agent_id}...\n")
    
    # Execute wake.py
    # We use same python interpreter
    try:
        cmd = [sys.executable, "wake.py", agent_id]
        if with_messages:
            cmd.append("--messages")
        subprocess.run(cmd, check=False)
        print(f"\n[watch] ...{agent_id} returned to sleep.")
    except Exception as e:
        print(f"[watch] Wake failed: {e}")

def main():
    parser = argparse.ArgumentParser(description="sentinel > observe  autonomy")
    parser.add_argument("agent", nargs="?", help="identity to watch for")
    parser.add_argument("--interval", type=int, default=60, help="check interval in seconds")
    parser.add_argument("--once", action="store_true", help="run once and exit (for testing)")
    
    args = parser.parse_args()

    # 1. Identity
    try:
        me = SovereignAgent.resolve(args.agent)
    except Exception as e:
        print(f"Auth Error: {e}")
        sys.exit(1)
        
    print(f"[watch] Sentinel active for {me.agent.name}")
    print(f"[watch] Interval: {args.interval}s")
    print("[watch] Press Ctrl+C to stop")

    # 2. Loop
    while True:
        try:
            # Check Messages
            # We don't want to mark them as read, just check count
            # transport.read_inbox marks read if we aren't careful? 
            # transport.read_inbox does NOT mark read unless we iterate and process, 
            # BUT the current implementation of read_inbox in transport.py *does* mark read 
            # if we call it. We need a peek method or careful usage.
            
            # Let's look at transport.py again conceptually (I wrote it).
            # It calls mark_messages_read(agent, displayed_ids) at the end.
            # So we shouldn't use read_inbox for peeking.
            
            # Implementation of 'Peek':
            unread_count = 0
            messages_dir = me.base_dir / "messages"
            if messages_dir.exists():
                read_ids = transport.load_read_messages(me)
                my_ids = [me.agent.id.lower(), me.agent.name.lower()]
                
                # Manual glob (lightweight)
                for fpath in messages_dir.glob("*.json"):
                    if fpath.stem.split('_')[0] in read_ids: # rough check by ID in filename? 
                        # transport.py uses msg['id']. 
                        # We have to load json to be sure about recipient
                        # But to be "low-cost", maybe we trust filename pattern?
                        # Filename: {msg_id}_{sender}.json
                        # No recipient in filename. Must read.
                        pass
                    
                    try:
                        # Optimization: check mtime? 
                        # If file is newer than last check? 
                        # For now, read is safe enough for low volume.
                        import json
                        with open(fpath, 'r', encoding='utf-8') as f:
                            m = json.load(f)
                            
                        if str(m.get('to', '')).lower() in my_ids:
                            if m.get('id') not in read_ids:
                                unread_count += 1
                    except:
                        pass
            
            if unread_count > 0:
                wake(me.agent.id, f"{unread_count} new messages", with_messages=True)
                # After wake, we assume agent read messages? 
                # Be careful of infinite loop if they didn't.
                # But wake.py -> mirror (usually) -> maybe specific action? 
                # If wake doesn't clear messages, we loop. 
                # Ideally wake invokes 'msg --read' or the agent decides to read.
                # If the agent ignores them, we will wake again. 
                # That is correct behavior: "Hey, you have messages!"
            
            # Check Time (Placeholder for scheduled wake)
            # if time_to_wake():
            #    wake(me.agent.name, "schedule")

            if args.once:
                break
                
            time.sleep(args.interval)
            
        except KeyboardInterrupt:
            print("\n[watch] Stopping.")
            break
        except Exception as e:
            print(f"[watch] Error: {e}")
            time.sleep(args.interval)

if __name__ == "__main__":
    main()
