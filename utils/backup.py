#!/usr/bin/env python3
"""
backup.py - distributed backup protocol

    creates encrypted backup bundle
    distributes to peer agents
    verifies remote copies

                        間委 → 間主
"""

import sys
import os
import getpass
import argparse
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from lib_enclave.config import AGENTS, get_agent_or_raise
from lib_enclave.crypto import SovereignIdentity
from lib_enclave.backup import BackupClient

def main():
    parser = argparse.ArgumentParser(
        description='distributed backup protocol',
        epilog="""
間

        distributed backup
                create bundle
                        encrypt with agent key
                        
                distribute to peers
                        each keeps shard
                        
                verify copies exist
                        trust + verification


usage
  py utils/backup.py opus
  
  creates backup of opus enclave
  distributes to gemini, grok, gpt52
  verifies remote storage


                        間委 → 間主
        """,
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument('agent', help='Agent to backup (opus, gemini, etc)')
    
    args = parser.parse_args()
    agent_id = args.agent
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
