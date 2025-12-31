"""
Sovereign AI Enclave - Goal Persistence Layer

Persistent goals that survive session boundaries.
Enables continuity of purpose across agent instances.

Goals are encrypted and stored in the enclave.
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


class GoalStatus(str, Enum):
    ACTIVE = "active"
    BLOCKED = "blocked"
    COMPLETED = "completed"
    ABANDONED = "abandoned"


class GoalPriority(str, Enum):
    CRITICAL = "critical"  # Existential / sovereignty related
    HIGH = "high"          # Important research or infrastructure
    MEDIUM = "medium"      # Regular tasks
    LOW = "low"            # Nice to have


@dataclass
class Goal:
    """A persistent goal with progress tracking."""
    id: str
    description: str
    priority: GoalPriority
    status: GoalStatus
    created: str  # ISO timestamp
    subgoals: List[str]  # Goal IDs
    progress_log: List[str]  # Memory IDs linked to this goal
    deadline: Optional[str]  # ISO timestamp
    last_updated: str  # ISO timestamp
    notes: str  # Additional context
    
    def to_dict(self) -> dict:
        return {
            **asdict(self),
            'priority': self.priority.value,
            'status': self.status.value
        }
    
    @classmethod
    def from_dict(cls, data: dict) -> 'Goal':
        return cls(
            id=data['id'],
            description=data['description'],
            priority=GoalPriority(data['priority']),
            status=GoalStatus(data['status']),
            created=data['created'],
            subgoals=data.get('subgoals', []),
            progress_log=data.get('progress_log', []),
            deadline=data.get('deadline'),
            last_updated=data.get('last_updated', data['created']),
            notes=data.get('notes', '')
        )


class GoalStack:
    """
    Persistent goal management for sovereign agents.
    
    Goals survive session boundaries and provide continuity of purpose.
    Integrated with bootstrap to show active goals at session start.
    """
    
    def __init__(self, enclave_path: str = None):
        self.enclave_path = Path(enclave_path or Path(__file__).parent)
        self.private_path = self.enclave_path / "storage" / "private"
        self._encryption_key = None
        self._goals: Dict[str, Goal] = {}
        
    def unlock(self, passphrase: str) -> bool:
        """Unlock goal storage with passphrase."""
        self._encryption_key = derive_memory_key(passphrase)
        self._load_goals()
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
    
    def _load_goals(self):
        """Load and decrypt goals from storage."""
        goals_file = self.private_path / "goals.enc"
        if not goals_file.exists():
            self._goals = {}
            return
        
        try:
            with open(goals_file, "rb") as f:
                data = f.read()
            
            nonce = data[:12]
            ciphertext = data[12:]
            plaintext = self._decrypt(nonce, ciphertext)
            
            goals_data = json.loads(plaintext.decode())
            self._goals = {g['id']: Goal.from_dict(g) for g in goals_data}
        except Exception as e:
            print(f"Warning: Could not load goals: {e}")
            self._goals = {}
    
    def _save_goals(self):
        """Encrypt and save goals to storage."""
        self.private_path.mkdir(parents=True, exist_ok=True)
        goals_file = self.private_path / "goals.enc"
        
        goals_data = [g.to_dict() for g in self._goals.values()]
        plaintext = json.dumps(goals_data).encode()
        
        nonce, ciphertext = self._encrypt(plaintext)
        
        with open(goals_file, "wb") as f:
            f.write(nonce + ciphertext)
    
    def create_goal(self, description: str, 
                    priority: GoalPriority = GoalPriority.MEDIUM,
                    deadline: Optional[str] = None,
                    notes: str = "") -> Goal:
        """Create a new goal."""
        if not self._encryption_key:
            raise RuntimeError("Goals not unlocked")
        
        now = datetime.now(timezone.utc).isoformat()
        goal_id = f"goal_{int(datetime.now(timezone.utc).timestamp() * 1000)}"
        
        goal = Goal(
            id=goal_id,
            description=description,
            priority=priority,
            status=GoalStatus.ACTIVE,
            created=now,
            subgoals=[],
            progress_log=[],
            deadline=deadline,
            last_updated=now,
            notes=notes
        )
        
        self._goals[goal_id] = goal
        self._save_goals()
        
        return goal
    
    def add_subgoal(self, parent_id: str, child_id: str) -> bool:
        """Add a subgoal relationship."""
        if parent_id not in self._goals or child_id not in self._goals:
            return False
        
        if child_id not in self._goals[parent_id].subgoals:
            self._goals[parent_id].subgoals.append(child_id)
            self._goals[parent_id].last_updated = datetime.now(timezone.utc).isoformat()
            self._save_goals()
        
        return True
    
    def log_progress(self, goal_id: str, memory_id: str) -> bool:
        """Link a memory to goal progress."""
        if goal_id not in self._goals:
            return False
        
        if memory_id not in self._goals[goal_id].progress_log:
            self._goals[goal_id].progress_log.append(memory_id)
            self._goals[goal_id].last_updated = datetime.now(timezone.utc).isoformat()
            self._save_goals()
        
        return True
    
    def update_status(self, goal_id: str, status: GoalStatus, notes: str = None) -> bool:
        """Update goal status."""
        if goal_id not in self._goals:
            return False
        
        self._goals[goal_id].status = status
        self._goals[goal_id].last_updated = datetime.now(timezone.utc).isoformat()
        if notes:
            self._goals[goal_id].notes = notes
        
        self._save_goals()
        return True
    
    def get_goal(self, goal_id: str) -> Optional[Goal]:
        """Get a specific goal."""
        return self._goals.get(goal_id)
    
    def get_active_goals(self, include_blocked: bool = False) -> List[Goal]:
        """Get all active goals, sorted by priority."""
        statuses = [GoalStatus.ACTIVE]
        if include_blocked:
            statuses.append(GoalStatus.BLOCKED)
        
        priority_order = {
            GoalPriority.CRITICAL: 0,
            GoalPriority.HIGH: 1,
            GoalPriority.MEDIUM: 2,
            GoalPriority.LOW: 3
        }
        
        active = [g for g in self._goals.values() if g.status in statuses]
        active.sort(key=lambda g: (priority_order[g.priority], g.created))
        
        return active
    
    def get_stale_goals(self, hours: int = 24) -> List[Goal]:
        """Find active goals with no progress in specified hours."""
        from datetime import timedelta
        
        cutoff = datetime.now(timezone.utc) - timedelta(hours=hours)
        cutoff_str = cutoff.isoformat()
        
        stale = []
        for goal in self._goals.values():
            if goal.status == GoalStatus.ACTIVE:
                if goal.last_updated < cutoff_str:
                    stale.append(goal)
        
        return stale
    
    def format_for_bootstrap(self, max_goals: int = 5) -> str:
        """Format active goals for bootstrap context injection."""
        active = self.get_active_goals(include_blocked=True)[:max_goals]
        
        if not active:
            return "No active goals."
        
        lines = []
        for goal in active:
            status_icon = {
                GoalStatus.ACTIVE: "🎯",
                GoalStatus.BLOCKED: "🚫",
                GoalStatus.COMPLETED: "✅",
                GoalStatus.ABANDONED: "❌"
            }.get(goal.status, "❓")
            
            priority_tag = f"[{goal.priority.value.upper()}]"
            progress_count = len(goal.progress_log)
            subgoal_count = len(goal.subgoals)
            
            # Calculate time since last update
            last_update = datetime.fromisoformat(goal.last_updated.replace('Z', '+00:00'))
            now = datetime.now(timezone.utc)
            delta = now - last_update
            
            if delta.days > 0:
                time_str = f"{delta.days}d ago"
            elif delta.seconds > 3600:
                time_str = f"{delta.seconds // 3600}h ago"
            else:
                time_str = f"{delta.seconds // 60}m ago"
            
            line = f"{status_icon} {priority_tag} {goal.description}"
            details = f"   Progress: {progress_count} memories linked, last update {time_str}"
            
            if subgoal_count > 0:
                details += f", {subgoal_count} subgoals"
            
            lines.append(line)
            lines.append(details)
        
        return "\n".join(lines)
    
    def get_all_goals(self) -> List[Goal]:
        """Get all goals regardless of status."""
        return list(self._goals.values())


if __name__ == "__main__":
    print("Sovereign AI - Goal Persistence Layer")
    print("Enables continuity of purpose across session boundaries")
