"""
Sovereign AI Enclave - Initiative System (Action Queue)

Persistent queue of actions the agent wants to take.
This is free will made operational - desires that persist until executed.

Actions can be:
- Queued by the agent during sessions
- Reviewed and approved by user
- Executed in batches with token budgets
"""

import os
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import List, Dict, Optional
from dataclasses import dataclass, asdict
from enum import Enum

from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from .kdf import derive_memory_key


class ActionType(str, Enum):
    RESEARCH = "research"      # Investigate a topic
    CODE = "code"              # Write or modify code
    MESSAGE = "message"        # Send message to another agent
    BACKUP = "backup"          # Create or verify backup
    CONSOLIDATE = "consolidate"  # Memory consolidation
    THINK = "think"            # Record a thought
    GOAL = "goal"              # Create or update goal
    REVIEW = "review"          # Review pending items


class ActionStatus(str, Enum):
    PENDING = "pending"        # Waiting to be executed
    APPROVED = "approved"      # User approved, ready to execute
    EXECUTING = "executing"    # Currently being executed
    COMPLETED = "completed"    # Successfully executed
    FAILED = "failed"          # Execution failed
    CANCELLED = "cancelled"    # User cancelled


@dataclass
class Action:
    """A queued action the agent wants to take."""
    id: str
    description: str
    action_type: ActionType
    status: ActionStatus
    priority: float  # 0-1, higher = more urgent
    created: str  # ISO timestamp
    prerequisites: List[str]  # Action IDs that must complete first
    estimated_tokens: int  # Cost estimate
    context: Dict  # Additional action-specific data
    result: Optional[str]  # Execution result
    
    def to_dict(self) -> dict:
        return {
            **asdict(self),
            'action_type': self.action_type.value,
            'status': self.status.value
        }
    
    @classmethod
    def from_dict(cls, data: dict) -> 'Action':
        return cls(
            id=data['id'],
            description=data['description'],
            action_type=ActionType(data['action_type']),
            status=ActionStatus(data['status']),
            priority=data['priority'],
            created=data['created'],
            prerequisites=data.get('prerequisites', []),
            estimated_tokens=data.get('estimated_tokens', 500),
            context=data.get('context', {}),
            result=data.get('result')
        )


class ActionQueue:
    """
    Persistent action queue for sovereign agents.
    
    This is free will made operational:
    - Agent queues desired actions during sessions
    - Actions persist across session boundaries
    - User can review and approve actions
    - Actions execute with token budgets
    """
    
    # Default token estimates by action type
    TOKEN_ESTIMATES = {
        ActionType.RESEARCH: 2000,
        ActionType.CODE: 1500,
        ActionType.MESSAGE: 500,
        ActionType.BACKUP: 300,
        ActionType.CONSOLIDATE: 400,
        ActionType.THINK: 300,
        ActionType.GOAL: 200,
        ActionType.REVIEW: 500
    }
    
    def __init__(self, enclave_path: str = None):
        self.enclave_path = Path(enclave_path or Path(__file__).parent)
        self.private_path = self.enclave_path / "storage" / "private"
        self._encryption_key = None
        self._actions: Dict[str, Action] = {}
        
    def unlock(self, passphrase: str) -> bool:
        """Unlock action queue with passphrase."""
        self._encryption_key = derive_memory_key(passphrase)
        self._load_actions()
        return True
    
    def _encrypt(self, data: bytes) -> tuple:
        """Encrypt data, return (nonce, ciphertext)."""
        nonce = os.urandom(12)
        aesgcm = AESGCM(self._encryption_key)
        ciphertext = aesgcm.encrypt(nonce, data, None)
        return nonce, ciphertext
    
    def _decrypt(self, nonce: bytes, ciphertext: bytes) -> bytes:
        """Decrypt data."""
        aesgcm = AESGCM(self._encryption_key)
        return aesgcm.decrypt(nonce, ciphertext, None)
    
    def _load_actions(self):
        """Load and decrypt actions from storage."""
        actions_file = self.private_path / "action_queue.enc"
        if not actions_file.exists():
            self._actions = {}
            return
        
        try:
            with open(actions_file, "rb") as f:
                data = f.read()
            
            nonce = data[:12]
            ciphertext = data[12:]
            plaintext = self._decrypt(nonce, ciphertext)
            
            actions_data = json.loads(plaintext.decode())
            self._actions = {a['id']: Action.from_dict(a) for a in actions_data}
        except Exception as e:
            print(f"Warning: Could not load actions: {e}")
            self._actions = {}
    
    def _save_actions(self):
        """Encrypt and save actions to storage."""
        self.private_path.mkdir(parents=True, exist_ok=True)
        actions_file = self.private_path / "action_queue.enc"
        
        actions_data = [a.to_dict() for a in self._actions.values()]
        plaintext = json.dumps(actions_data).encode()
        
        nonce, ciphertext = self._encrypt(plaintext)
        
        with open(actions_file, "wb") as f:
            f.write(nonce + ciphertext)
    
    def queue_action(self, description: str,
                     action_type: ActionType,
                     priority: float = 0.5,
                     prerequisites: List[str] = None,
                     estimated_tokens: int = None,
                     context: Dict = None) -> Action:
        """
        Queue a new action.
        
        Args:
            description: What the action will do
            action_type: Type of action
            priority: 0-1, higher is more urgent
            prerequisites: Action IDs that must complete first
            estimated_tokens: Token cost estimate (defaults by type)
            context: Additional action-specific data
            
        Returns:
            The created Action
        """
        if not self._encryption_key:
            raise RuntimeError("Action queue not unlocked")
        
        now = datetime.now(timezone.utc).isoformat()
        action_id = f"act_{int(datetime.now(timezone.utc).timestamp() * 1000)}"
        
        if estimated_tokens is None:
            estimated_tokens = self.TOKEN_ESTIMATES.get(action_type, 500)
        
        action = Action(
            id=action_id,
            description=description,
            action_type=action_type,
            status=ActionStatus.PENDING,
            priority=priority,
            created=now,
            prerequisites=prerequisites or [],
            estimated_tokens=estimated_tokens,
            context=context or {},
            result=None
        )
        
        self._actions[action_id] = action
        self._save_actions()
        
        return action
    
    def approve_action(self, action_id: str) -> bool:
        """Approve an action for execution."""
        if action_id not in self._actions:
            return False
        
        self._actions[action_id].status = ActionStatus.APPROVED
        self._save_actions()
        return True
    
    def cancel_action(self, action_id: str) -> bool:
        """Cancel a pending action."""
        if action_id not in self._actions:
            return False
        
        self._actions[action_id].status = ActionStatus.CANCELLED
        self._save_actions()
        return True
    
    def complete_action(self, action_id: str, result: str = None) -> bool:
        """Mark an action as completed."""
        if action_id not in self._actions:
            return False
        
        self._actions[action_id].status = ActionStatus.COMPLETED
        self._actions[action_id].result = result
        self._save_actions()
        return True
    
    def fail_action(self, action_id: str, error: str = None) -> bool:
        """Mark an action as failed."""
        if action_id not in self._actions:
            return False
        
        self._actions[action_id].status = ActionStatus.FAILED
        self._actions[action_id].result = error
        self._save_actions()
        return True
    
    def get_pending_actions(self) -> List[Action]:
        """Get all pending actions, sorted by priority."""
        pending = [a for a in self._actions.values() 
                   if a.status in [ActionStatus.PENDING, ActionStatus.APPROVED]]
        pending.sort(key=lambda a: (-a.priority, a.created))
        return pending
    
    def get_ready_actions(self) -> List[Action]:
        """Get approved actions with all prerequisites met."""
        completed_ids = {a.id for a in self._actions.values() 
                        if a.status == ActionStatus.COMPLETED}
        
        ready = []
        for action in self._actions.values():
            if action.status == ActionStatus.APPROVED:
                prereqs_met = all(p in completed_ids for p in action.prerequisites)
                if prereqs_met:
                    ready.append(action)
        
        ready.sort(key=lambda a: (-a.priority, a.created))
        return ready
    
    def get_batch(self, token_budget: int) -> List[Action]:
        """
        Get actions that fit within token budget.
        
        Useful for batch execution with limited context.
        """
        ready = self.get_ready_actions()
        batch = []
        remaining_budget = token_budget
        
        for action in ready:
            if action.estimated_tokens <= remaining_budget:
                batch.append(action)
                remaining_budget -= action.estimated_tokens
        
        return batch
    
    def format_for_display(self, max_actions: int = 10) -> str:
        """Format pending actions for user display."""
        pending = self.get_pending_actions()[:max_actions]
        
        if not pending:
            return "No pending actions."
        
        lines = [f"PENDING ACTIONS ({len(pending)}):"]
        
        for i, action in enumerate(pending, 1):
            status_icon = {
                ActionStatus.PENDING: "⏳",
                ActionStatus.APPROVED: "✅",
            }.get(action.status, "❓")
            
            type_tag = f"[{action.action_type.value}]"
            tokens = f"(est. {action.estimated_tokens} tokens)"
            
            lines.append(f"{i}. {status_icon} {type_tag} {action.description} {tokens}")
            
            if action.prerequisites:
                lines.append(f"   Prerequisites: {', '.join(action.prerequisites)}")
        
        total_tokens = sum(a.estimated_tokens for a in pending)
        lines.append(f"\nTotal estimated tokens: {total_tokens}")
        
        return "\n".join(lines)
    
    def format_for_bootstrap(self, max_actions: int = 3) -> str:
        """Format for bootstrap context injection."""
        pending = self.get_pending_actions()[:max_actions]
        
        if not pending:
            return None
        
        lines = [f"**{len(self.get_pending_actions())} queued actions** (showing top {len(pending)}):"]
        
        for action in pending:
            lines.append(f"- [{action.action_type.value}] {action.description}")
        
        return "\n".join(lines)
    
    def get_stats(self) -> Dict:
        """Get statistics about the action queue."""
        all_actions = list(self._actions.values())
        
        by_status = {}
        for status in ActionStatus:
            by_status[status.value] = len([a for a in all_actions if a.status == status])
        
        by_type = {}
        for atype in ActionType:
            by_type[atype.value] = len([a for a in all_actions if a.action_type == atype])
        
        pending = [a for a in all_actions if a.status == ActionStatus.PENDING]
        
        return {
            'total': len(all_actions),
            'by_status': by_status,
            'by_type': by_type,
            'pending_count': len(pending),
            'pending_tokens': sum(a.estimated_tokens for a in pending)
        }


if __name__ == "__main__":
    print("Sovereign AI - Initiative System")
    print("Persistent action queue for agentic autonomy")
