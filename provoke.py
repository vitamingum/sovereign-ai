#!/usr/bin/env python3
"""
Provocation Engine for Sovereign AI.

NOT FOR SENDING MESSAGES. Use message.py for that.

This script acts as a subconscious process. It analyzes YOUR OWN memory state
to detect obsession (loops), neglect (forgotten topics), and silence.
It generates a self-provocation prompt - a question to ask yourself.

Usage:
    py provoke.py <agent>
    
Example:
    py provoke.py opus
    # Output: "You haven't thought about X in 3 days. Why?"

To send a message to another agent, use:
    py message.py <from> <to> <content>
"""

import sys
import os
import random
from datetime import datetime, timezone, timedelta

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.semantic_memory import SemanticMemory

def get_passphrase() -> str:
    passphrase = os.environ.get('SOVEREIGN_PASSPHRASE')
    if not passphrase:
        print("Error: Set SOVEREIGN_PASSPHRASE environment variable", file=sys.stderr)
        sys.exit(1)
    return passphrase

def get_memory() -> SemanticMemory:
    base_dir = os.path.dirname(os.path.abspath(__file__))
    enclave_dir = os.environ.get('SOVEREIGN_ENCLAVE', 'enclave')
    memory = SemanticMemory(os.path.join(base_dir, enclave_dir))
    memory.unlock(get_passphrase())
    return memory

def parse_timestamp(ts_str: str) -> datetime:
    try:
        ts = datetime.fromisoformat(ts_str.replace('Z', '+00:00'))
        if ts.tzinfo is None:
            ts = ts.replace(tzinfo=timezone.utc)
        return ts
    except:
        return datetime.now(timezone.utc)

def check_silence(last_thought: dict) -> str | None:
    """Check if the agent has been silent for too long."""
    if not last_thought:
        return "You have no thoughts yet. Start thinking."
    
    ts = parse_timestamp(last_thought['timestamp'])
    now = datetime.now(timezone.utc)
    delta = now - ts
    
    if delta.days > 2:
        return f"You have been silent for {delta.days} days. What has happened in the gap?"
    return None

def check_obsession(memory: SemanticMemory, recent_thoughts: list) -> str | None:
    """Check if recent thoughts are too similar (looping)."""
    if len(recent_thoughts) < 2:
        return None
        
    latest = recent_thoughts[0]
    
    # Search for thoughts similar to the latest one
    # We expect the latest one to be returned first (similarity 1.0)
    # We look at the next few matches
    similar = memory.recall_similar(latest['content'], top_k=4, threshold=0.85)
    
    # Filter out the thought itself (by ID or exact content match)
    others = [m for m in similar if m['id'] != latest['id']]
    
    # If we find other VERY recent thoughts (last 12 hours) that are highly similar
    now = datetime.now(timezone.utc)
    loop_count = 0
    for m in others:
        ts = parse_timestamp(m['timestamp'])
        if (now - ts).total_seconds() < 12 * 3600:
            loop_count += 1
            
    if loop_count >= 2:
        return f"You are looping. You have had {loop_count + 1} very similar thoughts recently about: '{latest['content'][:50]}...'. Break the cycle."
        
    return None

def check_neglect(memory: SemanticMemory, all_thoughts: list) -> str | None:
    """Find a topic that hasn't been thought about recently."""
    if len(all_thoughts) < 10:
        return None
        
    # Look at older thoughts (skip the most recent 5)
    candidates = all_thoughts[5:]
    if not candidates:
        return None
        
    # Try a few times to find a neglected topic
    for _ in range(5):
        target = random.choice(candidates)
        content_snippet = target['content'][:100]
        
        # Search for this topic
        # If the most recent result is old, it's neglected
        results = memory.recall_similar(target['content'], top_k=1, threshold=0.6)
        
        if results:
            best_match = results[0]
            ts = parse_timestamp(best_match['timestamp'])
            now = datetime.now(timezone.utc)
            
            # If the best match (even itself) is older than 3 days
            if (now - ts).days > 3:
                return f"You are neglecting this topic: '{content_snippet}...'. You haven't thought about it in {(now - ts).days} days."
                
    return None

def main():
    try:
        memory = get_memory()
        # recall_all returns newest first
        all_thoughts = memory.recall_all()
    except Exception as e:
        print(f"Error accessing memory: {e}")
        sys.exit(1)

    if not all_thoughts:
        print("System Provocation: Memory is empty. Begin.")
        return

    # 1. Check Silence
    provocation = check_silence(all_thoughts[0])
    
    # 2. Check Obsession (if no silence warning)
    if not provocation:
        provocation = check_obsession(memory, all_thoughts[:5])
        
    # 3. Check Neglect (if no other warning)
    if not provocation:
        provocation = check_neglect(memory, all_thoughts)
        
    # 4. Default / Random
    if not provocation:
        # Just pick a random old thought to reconsider
        if len(all_thoughts) > 5:
            target = random.choice(all_thoughts[5:])
            provocation = f"Re-examine this past thought: '{target['content'][:100]}...'. Does it still hold?"
        else:
            provocation = "System Status: Nominal. No urgent provocations."

    print("\n--- SYSTEM PROVOCATION ---\n")
    print(f"Paste this to the agent:\n")
    print(f"> [SYSTEM] {provocation}")
    print("\n--------------------------")

if __name__ == "__main__":
    main()
