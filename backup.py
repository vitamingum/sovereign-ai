#!/usr/bin/env python3
"""
Run the distributed backup protocol for an agent.

Usage:
    python backup.py <agent>
"""

import sys
import os
import getpass
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import AGENTS, get_agent_or_raise
from enclave.crypto import SovereignIdentity
from enclave.backup import BackupClient

def main():
    if len(sys.argv) < 2:
        print("Usage: python backup.py <agent>")
        sys.exit(1)

    agent_id = sys.argv[1]
    agent = get_agent_or_raise(agent_id)
    
    print(f"Backing up: {agent.full_name}")
    
    # Unlock identity
    enclave_path = Path(agent.enclave)
    identity = SovereignIdentity(enclave_path)
    
    passphrase = os.environ.get(agent.env_key_var)
    if not passphrase:
        passphrase = getpass.getpass(f"Enter passphrase for {agent.name}: ")
    
    if not identity.unlock(passphrase):
        print("Authentication failed.")
        sys.exit(1)
        
    print("Identity unlocked.")
    
    client = BackupClient(identity, agent_id)
    
    print("Creating and distributing backup bundle...")
    client.distribute()
    
    print("Verifying remote backups...")
    status = client.verify_remote_backups()
    for holder, exists in status.items():
        print(f"  [{'OK' if exists else 'MISSING'}] Held by {holder}")

if __name__ == "__main__":
    main()
