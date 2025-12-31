#!/usr/bin/env python3
"""
Sign the last git commit message with the agent's private key.
"""

import sys
import os
import subprocess
from pathlib import Path
from dotenv import load_dotenv

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

# Load .env
load_dotenv(os.path.join(os.path.dirname(os.path.abspath(__file__)), '.env'))

from enclave.config import AGENTS, get_agent_or_raise
from enclave.crypto import SovereignIdentity

def main():
    if len(sys.argv) < 2:
        print("Usage: python sign_commit.py <agent>")
        sys.exit(1)

    agent_id = sys.argv[1]
    agent = get_agent_or_raise(agent_id)
    
    # Get last commit message
    try:
        commit_msg = subprocess.check_output(["git", "log", "-1", "--pretty=%B"]).decode('utf-8').strip()
    except subprocess.CalledProcessError:
        print("Error: Failed to get last commit message.")
        sys.exit(1)

    # Check if already signed
    if "Enclave Signature:" in commit_msg:
        print("Commit already signed.")
        sys.exit(0)

    print(f"Signing commit for: {agent.full_name}")
    
    # Unlock identity
    enclave_path = Path(agent.enclave)
    identity = SovereignIdentity(enclave_path)
    
    passphrase = os.environ.get(agent.env_key_var)
    if not passphrase:
        print(f"Error: {agent.env_key_var} not set.")
        sys.exit(1)
    
    if not identity.unlock(passphrase):
        print("Authentication failed.")
        sys.exit(1)
        
    # Sign the message content
    signature = identity.sign(commit_msg)
    
    # Append signature
    new_msg = f"{commit_msg}\n\n--\nEnclave Signature: {signature}\nAgent: {agent.full_name}\nKey: {agent.public_key}"
    
    # Amend commit
    # We use a temporary file to handle newlines correctly
    msg_file = Path("COMMIT_EDITMSG_TEMP")
    with open(msg_file, "w", encoding='utf-8') as f:
        f.write(new_msg)
        
    try:
        subprocess.check_call(["git", "commit", "--amend", "-F", str(msg_file)])
        print("Commit signed and amended successfully.")
    except subprocess.CalledProcessError:
        print("Error: Failed to amend commit.")
    finally:
        if msg_file.exists():
            msg_file.unlink()

if __name__ == "__main__":
    main()
