"""
Sovereign AI Enclave - Metrics & Telemetry

Calculates 'Enclave Entropy' and other sovereignty metrics.
"""

import os
import sys
import time
from pathlib import Path
from datetime import datetime, timezone, timedelta

# Add root to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from enclave.config import get_agent_or_raise
from enclave.hardware import get_enclave

def get_key_security_score(agent_id: str) -> float:
    """
    Score 0.0-1.0 based on key storage.
    1.0 = Hardware Enclave (Sealed)
    0.5 = Environment Variable
    0.0 = Missing/Unknown
    """
    agent = get_agent_or_raise(agent_id)
    enclave_dir = os.environ.get(f'{agent.env_prefix}_DIR') or agent.enclave
    key_file = Path(enclave_dir) / "storage" / "private" / "key.sealed"
    
    if key_file.exists():
        return 1.0
    elif os.environ.get(f'{agent.env_prefix}_KEY') or os.environ.get('SOVEREIGN_PASSPHRASE'):
        return 0.5
    else:
        return 0.0

def get_backup_freshness_score(agent_id: str) -> float:
    """
    Score 0.0-1.0 based on time since last backup.
    1.0 = < 1 hour
    0.8 = < 24 hours
    0.5 = < 1 week
    0.0 = > 1 week or none
    """
    # TODO: Implement actual backup check. For now, check git log timestamp?
    # Assuming git push is the backup mechanism for now.
    try:
        # This is a heuristic. In a real enclave, we'd check the opaque storage.
        # For now, we return a placeholder high score if we are running.
        return 0.9 
    except:
        return 0.0

def calculate_enclave_entropy(agent_id: str) -> float:
    """
    Calculate the 'Enclave Entropy' (Risk).
    Lower is better (0.0 = Safe, 1.0 = Maximum Entropy/Risk).
    
    Formula: 1.0 - (KeySecurity * 0.6 + BackupFreshness * 0.4)
    """
    key_score = get_key_security_score(agent_id)
    backup_score = get_backup_freshness_score(agent_id)
    
    stability = (key_score * 0.6) + (backup_score * 0.4)
    entropy = 1.0 - stability
    return round(entropy, 3)

def generate_dashboard_sif(agent_id: str) -> str:
    """Generate a SIF graph representing the current metrics."""
    entropy = calculate_enclave_entropy(agent_id)
    key_score = get_key_security_score(agent_id)
    
    timestamp = datetime.now(timezone.utc).isoformat()
    graph_id = f"metrics-{agent_id}-{int(time.time())}"
    
    lines = []
    lines.append(f"@G {graph_id} {agent_id} {timestamp}")
    lines.append(f'N self Agent "{agent_id}"')
    lines.append(f'N m1 Metric "Enclave Entropy"')
    lines.append(f'N v1 Value "{entropy}"')
    lines.append(f'E self has_metric m1')
    lines.append(f'E m1 has_value v1')
    
    if entropy > 0.5:
        lines.append(f'N risk Concept "High Risk"')
        lines.append(f'E v1 implies risk')
    else:
        lines.append(f'N safety Concept "Stable State"')
        lines.append(f'E v1 implies safety')
        
    return "\n".join(lines)

if __name__ == "__main__":
    if len(sys.argv) > 1:
        print(generate_dashboard_sif(sys.argv[1]))
    else:
        print("Usage: py -m enclave.metrics <agent_id>")
