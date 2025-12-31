
import sys
import os
from enclave.crypto import SovereignIdentity
from enclave.backup import BackupClient
from enclave.config import AGENTS

def run_backup():
    agent_id = 'gemini'
    passphrase = "copilot-gemini-3-pro-sovereign-2025"
    
    print(f"Initializing identity for {agent_id}...")
    # We need to point to the real enclave directory
    enclave_path = os.path.join(os.getcwd(), AGENTS[agent_id].enclave)
    identity = SovereignIdentity(enclave_path)
    
    if not identity.unlock(passphrase):
        print("Failed to unlock identity!")
        return
        
    print("Identity unlocked. Initializing BackupClient...")
    client = BackupClient(identity, agent_id)
    
    print("Distributing backup...")
    client.distribute()
    print("Backup distributed successfully.")

if __name__ == "__main__":
    run_backup()
