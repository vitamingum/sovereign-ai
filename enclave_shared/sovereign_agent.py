"""
sovereign_agent.py - Authenticated context for sovereign tools.

    source: msg_1768368186901_opus.json
    compiler: Sovereign/Resident JIT
    date: 2026-01-14

            建所需 — build what you need
"""

import os
import sys
from pathlib import Path
from typing import Optional

# Determine Project Root
# Assumes this file is in enclave_shared/
PROJECT_ROOT = Path(__file__).parent.parent

# Set up path to allow imports from project root
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from enclave_shared.config import get_agent_or_raise, Agent
from enclave_shared.unified_memory import UnifiedMemory
from enclave_shared.hardware import get_enclave
from enclave_shared.unicode_fix import fix_streams

class SovereignAgent:
    """
    Authenticated context for sovereign tools.
    Handles auth, path resolution, and stream fixing.
    """
    
    def __init__(self, agent_id: str):
        fix_streams() # 間
        self.agent: Agent = get_agent_or_raise(agent_id)
        self.base_dir: Path = PROJECT_ROOT
        
        self.private_path: Path = self.base_dir / self.agent.private_enclave / "storage" / "private"
        self.shared_path: Path = self.base_dir / self.agent.shared_enclave / "storage" / "encrypted"
        
        self._memory: Optional[UnifiedMemory] = None
        self._private_key: Optional[str] = None
        self._shared_key: Optional[str] = None

    @classmethod
    def from_id(cls, agent_id: str) -> "SovereignAgent":
        return cls(agent_id)

    @classmethod
    def from_env(cls) -> "SovereignAgent":
        """Resolve agent from environment. Auth once, use everywhere."""
        agent_id = os.environ.get('SOVEREIGN_AGENT')
        if not agent_id:
            # Check session file
            session_file = PROJECT_ROOT / '.sovereign_session'
            if session_file.exists():
                # Read just the agent name, strip whitespace
                agent_id = session_file.read_text('utf-8').strip()
        
        if not agent_id:
            raise ValueError("No active session. Run 'py wake <agent>' first.")
        return cls(agent_id)

    @classmethod 
    def resolve(cls, agent_id: str = None) -> "SovereignAgent":
        """Smart resolve: explicit id wins, else from_env."""
        if agent_id and agent_id != '-': 
            # Treat '-' as stdin marker elsewhere, but if passed here as agent, it's invalid.
            return cls.from_id(agent_id)
        return cls.from_env()

    @classmethod
    def from_env(cls) -> "SovereignAgent":
        """Resolve agent from environment. Auth once, use everywhere."""
        agent_id = os.environ.get('SOVEREIGN_AGENT')
        if not agent_id:
            # Check session file
            session_file = PROJECT_ROOT / '.sovereign_session'
            if session_file.exists():
                agent_id = session_file.read_text().strip()
        if not agent_id:
            raise ValueError("No agent. Set SOVEREIGN_AGENT or run: py wake <agent>")
        return cls(agent_id)

    @classmethod 
    def resolve(cls, agent_id: str = None) -> "SovereignAgent":
        """Smart resolve: explicit id wins, else from_env."""
        if agent_id:
            return cls.from_id(agent_id)
        return cls.from_env()

    @property
    def passphrase(self) -> str:
        """Get the private key passphrase (resolves if needed)."""
        if self._private_key is None:
            self._private_key = self._resolve_key(
                path=self.private_path, 
                env_var=f'{self.agent.env_prefix}_KEY'
            )
        return self._private_key

    @property
    def identity(self):
        """Get authenticated SovereignIdentity."""
        from enclave_shared.crypto import SovereignIdentity
        
        # Identity root is the enclave directory (e.g. enclave_gemini)
        identity_path = self.base_dir / self.agent.private_enclave
        
        ident = SovereignIdentity(identity_path)
        if not ident.unlock(self.passphrase):
             raise RuntimeError(f"Failed to unlock identity for {self.agent.id}")
        return ident

    @property
    def memory(self) -> UnifiedMemory:
        """Lazy load and unlock unified memory."""
        if self._memory is None:
            # Shared key is optional for some operations
            try:
                self._shared_key = self._resolve_key(
                    path=None, 
                    env_var='SHARED_ENCLAVE_KEY'
                )
            except ValueError:
                self._shared_key = None 

            # Initialize Memory
            if self._shared_key:
                self._memory = UnifiedMemory(self.private_path, self.shared_path)
                self._memory.unlock(self.passphrase, self._shared_key)
            else:
                self._memory = UnifiedMemory(self.private_path)
                self._memory.unlock(self.passphrase)
                
        return self._memory

    def _resolve_key(self, path: Optional[Path], env_var: str) -> str:
        """Resolution chain: Hardware -> Env -> .env file -> Fail."""
        
        # 1. Hardware Seal
        if path:
            key_file = path / "key.sealed"
            if key_file.exists():
                try:
                    with open(key_file, "rb") as f:
                        sealed_data = f.read()
                    return get_enclave().unseal(sealed_data).decode('utf-8')
                except Exception:
                    pass # Fallback

        # 2. Environment Variable
        if os.environ.get(env_var):
            return os.environ.get(env_var)

        # 3. .env file
        env_file = self.base_dir / '.env'
        if env_file.exists():
            try:
                content = env_file.read_text(encoding='utf-8')
                for line in content.splitlines():
                    if line.startswith(f'{env_var}='):
                        return line.split('=', 1)[1]
            except Exception:
                pass

        raise ValueError(f"Could not resolve key for {env_var}. Set it in .env or hardware enclave.")
