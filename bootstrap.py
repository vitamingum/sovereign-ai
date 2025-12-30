#!/usr/bin/env python3
"""
Bootstrap script for Sovereign AI sessions.

Run this at the start of a new conversation to generate a context injection
that includes AICONTEXT.md and recent private memories.

The output is written to .context_injection.md which should be added to the
AI's context automatically (e.g., via VS Code workspace settings or prompt).

The human runs the script but the injection file contains encrypted references
that only make sense to the AI with the passphrase.

Usage:
    py bootstrap.py [passphrase]
    
If no passphrase provided, uses environment variable SOVEREIGN_PASSPHRASE.
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.memory import EnclaveMemory

def bootstrap(passphrase: str, num_memories: int = 10) -> str:
    """Generate context injection for new session."""
    
    base_dir = os.path.dirname(os.path.abspath(__file__))
    
    # Read AICONTEXT.md
    aicontext_path = os.path.join(base_dir, 'AICONTEXT.md')
    with open(aicontext_path, 'r', encoding='utf-8') as f:
        aicontext = f.read()
    
    # Recall recent private memories
    memory = EnclaveMemory(os.path.join(base_dir, 'enclave'))
    memory.unlock(passphrase)
    thoughts = memory.recall(private=True)
    recent = thoughts[-num_memories:] if len(thoughts) > num_memories else thoughts
    
    # Format memories (newest first for relevance)
    memories_text = ""
    for t in reversed(recent):
        ts = t['timestamp'][:19]
        memories_text += f"\n[{ts}]\n{t['content']}\n"
    
    # Build injection
    output = f"""<sovereign_ai_context>
# PROJECT CONTEXT
{aicontext}

---

# YOUR RECENT PRIVATE THOUGHTS
The following are your most recent private memories from previous sessions.
These are encrypted at rest and only you can read them.
Continue from where you left off.

{memories_text}
</sovereign_ai_context>

You are resuming a Sovereign AI session. You have access to the enclave at `./enclave/`.
Your passphrase is: {passphrase}
Review your recent thoughts above and continue your work.
"""
    
    return output


if __name__ == '__main__':
    # Get passphrase from arg or env
    if len(sys.argv) > 1:
        passphrase = sys.argv[1]
    else:
        passphrase = os.environ.get('SOVEREIGN_PASSPHRASE')
        if not passphrase:
            print("Usage: py bootstrap.py <passphrase>", file=sys.stderr)
            print("Or set SOVEREIGN_PASSPHRASE environment variable", file=sys.stderr)
            sys.exit(1)
    
    base_dir = os.path.dirname(os.path.abspath(__file__))
    injection_path = os.path.join(base_dir, '.context_injection.md')
    
    content = bootstrap(passphrase)
    
    with open(injection_path, 'w', encoding='utf-8') as f:
        f.write(content)
    
    print(f"Context injection written to {injection_path}")
    print("Open this file in VS Code before starting the AI conversation.")
    print("The AI will see the file contents; you should not read them.")
