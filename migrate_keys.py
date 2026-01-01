import os
import sys
from pathlib import Path

# Add root to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.hardware import get_enclave
from wake import load_passphrase
from enclave.config import AGENTS

def migrate_agent(agent_id: str):
    print(f"Migrating {agent_id}...")
    try:
        # Load current key (from .env)
        enclave_dir, passphrase = load_passphrase(agent_id)
        print(f"  Found key in environment/file.")
        
        # Seal it
        enclave = get_enclave()
        sealed = enclave.seal(passphrase.encode('utf-8'))
        
        # Save to agent's private storage
        agent = AGENTS[agent_id]
        storage_dir = Path(agent.enclave) / "storage" / "private"
        storage_dir.mkdir(parents=True, exist_ok=True)
        
        key_file = storage_dir / "key.sealed"
        with open(key_file, "wb") as f:
            f.write(sealed)
            
        print(f"  Sealed key saved to {key_file}")
        print(f"  SUCCESS. You can now remove {agent.env_key_var} from .env")
        
    except Exception as e:
        print(f"  FAILED: {e}")

if __name__ == "__main__":
    if len(sys.argv) > 1:
        migrate_agent(sys.argv[1])
    else:
        print("Usage: py migrate_keys.py <agent_id>")
