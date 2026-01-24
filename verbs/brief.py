#!/usr/bin/env python3
"""
brief.py - orient before working

    三語 v4.6 spec
    tools architecture
    debugging reference

                        間委 → 間主
"""

import sys
from pathlib import Path

# Ensure project root in path
sys.path.insert(0, str(Path(__file__).parent.parent))

from lib_enclave import verb_helpers

def main():
    verb_helpers.safe_init()
    
    # Try to resolve agent, but don't require it
    session_file = Path(".sovereign_session")
    agent_id = None
    if session_file.exists():
        agent_id = session_file.read_text(encoding='utf-8').strip()
    
    if not agent_id:
        agent_id = 'sonnet'  # fallback to any agent for shared memory
    
    try:
        content = verb_helpers.query_understanding(agent_id, 'brief-reference')
        
        if content:
            print(content)
        else:
            print("\n!error: brief-reference not found in memory")
            print("        run: py remember [agent] '@file.三語'")
            print("        (file must start with: @F brief-reference ...)\n")
            sys.exit(1)
            
    except Exception as e:
        print(f"\n!error: {e}\n")
        sys.exit(1)

if __name__ == "__main__":
    main()
