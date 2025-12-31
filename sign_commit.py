#!/usr/bin/env python3
"""
Sign the last git commit message with the agent's private key.

Usage:
    python sign_commit.py <agent> [--force] [--commit <rev>]

Notes:
    - By default signs HEAD.
    - If the commit already contains an "Enclave Signature:" footer, the script
      exits unless --force is provided.
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


def strip_enclave_signature_block(message: str) -> str:
    """Remove an existing Sovereign AI signature footer, if present."""
    marker = "\n--\nEnclave Signature:"
    alt_marker = "\n\n--\nEnclave Signature:"

    idx = message.find(alt_marker)
    if idx != -1:
        return message[:idx].rstrip()

    idx = message.find(marker)
    if idx != -1:
        return message[:idx].rstrip()

    return message.rstrip()

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    agent_id = None
    force = False
    commit_rev = "HEAD"

    args = sys.argv[1:]
    i = 0
    while i < len(args):
        arg = args[i]
        if arg == "--force":
            force = True
            i += 1
            continue
        if arg == "--commit":
            if i + 1 >= len(args):
                print("Error: --commit requires a revision (e.g., HEAD)")
                sys.exit(1)
            commit_rev = args[i + 1]
            i += 2
            continue
        if agent_id is None and not arg.startswith("--"):
            agent_id = arg
            i += 1
            continue
        print(f"Unknown argument: {arg}")
        print(__doc__)
        sys.exit(1)

    if not agent_id:
        print(__doc__)
        sys.exit(1)

    agent = get_agent_or_raise(agent_id)
    
    # Get last commit message
    try:
        commit_msg = subprocess.check_output(["git", "log", "-1", commit_rev, "--pretty=%B"]).decode('utf-8').strip()
    except subprocess.CalledProcessError:
        print("Error: Failed to get last commit message.")
        sys.exit(1)

    # Check if already signed
    if "Enclave Signature:" in commit_msg and not force:
        print("Commit already signed. Use --force to replace the signature.")
        sys.exit(0)

    if force:
        commit_msg = strip_enclave_signature_block(commit_msg)

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
        if commit_rev != "HEAD":
            print("Error: Can only amend/sign HEAD. Re-run with --commit HEAD or checkout the desired commit.")
            sys.exit(1)
        subprocess.check_call(["git", "commit", "--amend", "-F", str(msg_file)])
        print("Commit signed and amended successfully.")
    except subprocess.CalledProcessError:
        print("Error: Failed to amend commit.")
    finally:
        if msg_file.exists():
            msg_file.unlink()

if __name__ == "__main__":
    main()
