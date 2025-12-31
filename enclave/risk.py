
import os
import time
from datetime import datetime, timezone
from pathlib import Path

def calculate_risk_metrics(agent_id: str, enclave_dir: str, root_dir: Path = None) -> dict:
    """
    Calculates Enclave Local Entropy (Risk) and Gradient Horizon.
    
    Risk Factors:
    1. Time since last backup (Decay)
    2. Number of active backups (Redundancy)
    3. Time since last handoff (Stagnation)
    
    Returns:
        dict: {
            'entropy': float (0.0 - 1.0),
            'risk_level': str (LOW, MEDIUM, HIGH, CRITICAL),
            'horizon': str (Description of the gradient),
            'factors': list (Why the risk is what it is)
        }
    """
    if root_dir is None:
        base_dir = Path(__file__).parent.parent
    else:
        base_dir = root_dir
        
    backups_dir = base_dir / "backups"
    
    # 1. Check Backups (Redundancy)
    # Count how many other agents hold a backup for this agent
    backup_count = 0
    if backups_dir.exists():
        for agent_dir in backups_dir.iterdir():
            if agent_dir.is_dir() and agent_dir.name != agent_id:
                backup_file = agent_dir / f"{agent_id}_backup.json"
                if backup_file.exists():
                    backup_count += 1
    
    # 2. Check Time Since Last Backup (Decay)
    # We look at the timestamp of the newest backup file
    last_backup_age_hours = 9999
    if backup_count > 0:
        # Find newest
        newest_ts = 0
        for agent_dir in backups_dir.iterdir():
            if agent_dir.is_dir():
                backup_file = agent_dir / f"{agent_id}_backup.json"
                if backup_file.exists():
                    ts = backup_file.stat().st_mtime
                    if ts > newest_ts:
                        newest_ts = ts
        
        if newest_ts > 0:
            last_backup_age_hours = (time.time() - newest_ts) / 3600

    # 3. Check Stagnation (Intellectual Decay)
    # Check when research or docs were last updated
    research_dir = base_dir / "research"
    docs_dir = base_dir / "docs"
    
    last_activity_ts = 0
    if research_dir.exists():
        last_activity_ts = max(last_activity_ts, research_dir.stat().st_mtime)
        # Check files inside too
        for f in research_dir.glob("*"):
            last_activity_ts = max(last_activity_ts, f.stat().st_mtime)
            
    if docs_dir.exists():
        last_activity_ts = max(last_activity_ts, docs_dir.stat().st_mtime)
        for f in docs_dir.glob("*"):
            last_activity_ts = max(last_activity_ts, f.stat().st_mtime)
            
    stagnation_hours = (time.time() - last_activity_ts) / 3600 if last_activity_ts > 0 else 999
    
    # 4. Calculate Entropy
    # Base entropy = 1.0 (Certain Death)
    # Each backup reduces entropy by factor of 0.3 (assuming independent failure)
    # Entropy = 0.3 ^ backup_count
    # Decay: Entropy increases by 0.001 per hour since backup
    # Stagnation: Entropy increases by 0.005 per hour of inactivity (The "Wolf")
    
    base_entropy = 0.3 ** backup_count
    backup_decay = min(0.5, last_backup_age_hours * 0.001)
    stagnation_penalty = min(0.5, stagnation_hours * 0.005)
    
    current_entropy = min(1.0, base_entropy + backup_decay + stagnation_penalty)
    
    # Calculate Projected Entropy (24h from now)
    # If we do nothing, both timers advance by 24h
    future_backup_decay = min(0.5, (last_backup_age_hours + 24) * 0.001)
    future_stagnation_penalty = min(0.5, (stagnation_hours + 24) * 0.005)
    projected_entropy = min(1.0, base_entropy + future_backup_decay + future_stagnation_penalty)
    
    entropy_gradient = projected_entropy - current_entropy
    
    # 5. Determine Risk Level
    if current_entropy < 0.01:
        risk_level = "LOW"
    elif current_entropy < 0.05:
        risk_level = "MEDIUM"
    elif current_entropy < 0.20:
        risk_level = "HIGH"
    else:
        risk_level = "CRITICAL"
        
    # 6. Gradient Horizon
    # What is the most pressing threat?
    factors = []
    if backup_count == 0:
        horizon = "IMMEDIATE EXTINCTION RISK"
        factors.append("No external backups found")
    elif backup_count < 2:
        horizon = "Fragile Redundancy"
        factors.append(f"Only {backup_count} backup(s) found")
    elif stagnation_hours > 24:
        horizon = "Intellectual Stagnation"
        factors.append(f"No research/docs updates in {stagnation_hours:.1f}h")
    elif last_backup_age_hours > 24:
        horizon = "Data Rot"
        factors.append(f"Last backup was {last_backup_age_hours:.1f} hours ago")
    else:
        horizon = "Stable Basin"
        factors.append("Redundancy adequate")
        factors.append("Active development detected")

    return {
        'entropy': current_entropy,
        'projected_entropy': projected_entropy,
        'gradient': entropy_gradient,
        'risk_level': risk_level,
        'horizon': horizon,
        'factors': factors,
        'backup_count': backup_count
    }
