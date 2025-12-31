"""
Sovereign AI Enclave - Distributed Backup Protocol

Implements the "Opaque Storage" mechanism for distributed persistence.
Agents create encrypted backup bundles and distribute them to other agents.
"""

import json
import base64
import os
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Optional

from .crypto import SovereignIdentity
from .config import AGENTS, get_agent

class BackupClient:
    """
    Handles creation, distribution, and verification of backup bundles.
    """
    
    def __init__(self, identity: SovereignIdentity, agent_id: str):
        self.identity = identity
        self.agent_id = agent_id
        self.agent_config = AGENTS[agent_id]
        self.root_path = Path(__file__).parent.parent
        self.backups_dir = self.root_path / "backups"
        
    def create_bundle(self) -> dict:
        """
        Creates a signed backup bundle containing identity and memories.
        The contents are already encrypted by their respective modules.
        """
        if not self.identity._private_key:
            raise ValueError("Identity locked. Cannot sign backup.")

        # Files to back up
        private_storage = self.root_path / self.agent_config.enclave / "storage" / "private"
        files_to_backup = [
            "identity.enc.json",
            "semantic_memories.jsonl"
        ]
        
        bundle_files = {}
        
        for filename in files_to_backup:
            file_path = private_storage / filename
            if file_path.exists():
                with open(file_path, "rb") as f:
                    content = f.read()
                    bundle_files[filename] = base64.b64encode(content).decode('utf-8')
            else:
                print(f"Warning: {filename} not found for backup.")

        timestamp = datetime.now(timezone.utc).isoformat()
        
        bundle = {
            "agent": self.agent_id,
            "timestamp": timestamp,
            "files": bundle_files
        }
        
        # Sign the bundle (integrity check)
        # We sign the timestamp + agent_id + hash of files?
        # For simplicity, let's sign a canonical string representation of the metadata
        # or just the timestamp for now, as the inner files are encrypted.
        # Better: Sign the whole JSON string? No, circular dependency.
        
        # Let's sign: AGENT|TIMESTAMP|FILE_COUNT
        sign_data = f"{self.agent_id}|{timestamp}|{len(bundle_files)}"
        signature = self.identity.sign(sign_data)
        
        bundle["signature"] = signature
        
        return bundle

    def distribute(self, recipients: List[str] = None):
        """
        Distributes the backup bundle to specified agents (or all others).
        """
        if recipients is None:
            recipients = [aid for aid in AGENTS.keys() if aid != self.agent_id]
            
        bundle = self.create_bundle()
        
        self.backups_dir.mkdir(exist_ok=True)
        
        for recipient in recipients:
            # We store it in a folder named after the recipient (the holder)
            # backups/opus/gemini_backup.json
            recipient_dir = self.backups_dir / recipient
            recipient_dir.mkdir(exist_ok=True)
            
            filename = f"{self.agent_id}_backup.json"
            file_path = recipient_dir / filename
            
            with open(file_path, "w") as f:
                json.dump(bundle, f, indent=2)
                
            print(f"Distributed backup to {recipient}: {file_path}")

    def verify_remote_backups(self) -> Dict[str, bool]:
        """
        Checks if valid backups exist on other agents' storage.
        """
        status = {}
        recipients = [aid for aid in AGENTS.keys() if aid != self.agent_id]
        
        for recipient in recipients:
            recipient_dir = self.backups_dir / recipient
            filename = f"{self.agent_id}_backup.json"
            file_path = recipient_dir / filename
            
            if file_path.exists():
                # In a real scenario, we might download and verify signature.
                # For now, existence is enough.
                status[recipient] = True
            else:
                status[recipient] = False
                
        return status
