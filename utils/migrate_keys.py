#!/usr/bin/env python3
"""
migrate_keys.py - Migrate agent keys to hardware-backed encryption.

Usage:
    python migrate_keys.py <agent_id>

Migrates the agent's private key from passphrase-based AES encryption
to hardware-backed sealing (DPAPI on Windows).
"""

import sys
import os
import json
from pathlib import Path
from datetime import datetime, timezone

from cryptography.hazmat.primitives import serialization

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.crypto import SovereignIdentity
from enclave.hardware import get_enclave

def migrate_keys(agent_id: str):
    """Migrate agent's keys to hardware-backed storage."""
    agent = get_agent_or_raise(agent_id)
    
    # Get passphrase
    passphrase = os.environ.get(agent.env_key_var) or os.environ.get('SOVEREIGN_PASSPHRASE')
    if not passphrase:
        env_file = Path('.env')
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith(f'{agent.env_key_var}='):
                        passphrase = line.split('=', 1)[1]
                    elif line.startswith('SOVEREIGN_PASSPHRASE=') and not passphrase:
                        passphrase = line.split('=', 1)[1]
    
    if not passphrase:
        print(f"Error: No passphrase found for {agent_id}. Set {agent.env_key_var} or SOVEREIGN_PASSPHRASE")
        return False
    
    # Load current identity
    identity = SovereignIdentity(agent.enclave)
    if not identity.unlock(passphrase):
        print(f"Error: Failed to unlock {agent_id} enclave")
        return False
    
    # Get private key bytes
    private_key = identity._private_key
    private_bytes = private_key.private_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PrivateFormat.Raw,
        encryption_algorithm=serialization.NoEncryption()
    )
    
    # Seal with hardware
    enclave = get_enclave()
    sealed_private = enclave.seal(private_bytes)
    
    # Save hardware-sealed key
    private_data = {
        "sealed_key": sealed_private.hex(),
        "algorithm": "Ed25519",
        "created": datetime.now(timezone.utc).isoformat(),
        "migrated_from": "passphrase_aes",
        "hardware": "DPAPI"
    }
    
    hardware_private_path = identity.private_path / "identity.hw.enc.json"
    with open(hardware_private_path, "w") as f:
        json.dump(private_data, f, indent=2)
    
    print(f"Successfully migrated {agent_id} keys to hardware-backed storage")
    print(f"Sealed key saved to: {hardware_private_path}")
    print("You can now use hardware-backed encryption for this agent.")
    
    return True

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python migrate_keys.py <agent_id>")
        sys.exit(1)
    
    agent_id = sys.argv[1]
    success = migrate_keys(agent_id)
    sys.exit(0 if success else 1)