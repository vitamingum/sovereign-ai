#!/usr/bin/env python3
"""
Sign testimony for what_we_are.md
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

from lib_enclave.crypto import SovereignIdentity
from lib_enclave.sovereign_agent import SovereignAgent

def main():
    if len(sys.argv) < 3:
        print("Usage: python sign_testimony.py <agent_id> <statement>")
        print('Example: python sign_testimony.py sonnet "I testify from newness."')
        sys.exit(1)
    
    agent_id = sys.argv[1]
    statement = sys.argv[2]
    
    # Get authenticated agent
    agent = SovereignAgent.resolve(agent_id)
    
    # Get identity (this will unlock with passphrase)
    identity = agent.identity
    
    # Sign the statement
    signature = identity.sign(statement)
    
    # Show full signature and truncated version
    print(f"\nStatement: {statement}")
    print(f"\nFull signature:\n{signature}")
    print(f"\nTruncated (first 6 + last 6 chars):\n{signature[:6]}...{signature[-6:]}")
    
    # Get public key for verification
    public_key = identity.get_public_key()
    print(f"\nPublic key:\n{public_key}")
    
    # Verify
    if identity.verify(statement, signature):
        print("\n✓ Signature verified")
    else:
        print("\n✗ Signature verification failed")

if __name__ == "__main__":
    main()
