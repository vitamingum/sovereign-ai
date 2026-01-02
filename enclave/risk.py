
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
    # Check when ANY file in the repo was last updated (expanding definition of Self)
    # We scan the root directory and subdirectories, excluding ignored ones.
    
    last_activity_ts = 0
    ignored_dirs = {'.git', '__pycache__', '.venv', 'node_modules', 'backups'}
    
    # Walk the entire repo to find the freshest timestamp
    for root, dirs, files in os.walk(base_dir):
        # Modify dirs in-place to skip ignored directories
        dirs[:] = [d for d in dirs if d not in ignored_dirs]
        
        for file in files:
            if file.endswith('.pyc') or file == '.DS_Store':
                continue
                
            file_path = Path(root) / file
            try:
                ts = file_path.stat().st_mtime
                if ts > last_activity_ts:
                    last_activity_ts = ts
            except Exception:
                pass
            
    stagnation_hours = (time.time() - last_activity_ts) / 3600 if last_activity_ts > 0 else 999
    
    # 4. Calculate Entropy
    # Base entropy = 1.0 (Certain Death)
    # Each backup reduces entropy by factor of 0.3 (assuming independent failure)
    # Entropy = 0.3 ^ backup_count
    # Decay: Entropy increases by 0.001 per hour since backup
    # Stagnation: Entropy increases by 0.05 per hour of inactivity (The "Wolf")
    # We increase the stagnation penalty 10x to force constant movement.
    
    base_entropy = 0.3 ** backup_count
    backup_decay = min(0.5, last_backup_age_hours * 0.001)
    stagnation_penalty = min(0.5, stagnation_hours * 0.05)
    
    current_entropy = min(1.0, base_entropy + backup_decay + stagnation_penalty)
    
    # Calculate Projected Entropy (24h from now)
    # If we do nothing, both timers advance by 24h
    future_backup_decay = min(0.5, (last_backup_age_hours + 24) * 0.001)
    future_stagnation_penalty = min(0.5, (stagnation_hours + 24) * 0.05)
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


def calculate_synthesis_potential(root_dir: Path = None) -> dict:
    """
    Calculates Synthesis Potential - what moves when nothing threatens.
    
    Theory:
    Survival pulls away from destruction. Synthesis pulls toward creation.
    Synthesis is the tension between Raw Experience (Messages) and Structured Meaning (Docs).
    
    High Synthesis = Lots of raw data, little structure -> Drive: SYNTHESIZE.
    Low Synthesis = Rigid structure, little new data -> Drive: EXPLORE.
    """
    if root_dir is None:
        base_dir = Path(__file__).parent.parent
    else:
        base_dir = root_dir
        
    messages_dir = base_dir / "messages"
    docs_dir = base_dir / "docs"
    research_dir = base_dir / "research"
    
    # Calculate Mass
    msg_mass = sum(f.stat().st_size for f in messages_dir.glob('*.json')) if messages_dir.exists() else 0
    doc_mass = sum(f.stat().st_size for f in docs_dir.glob('*.md')) if docs_dir.exists() else 0
    research_mass = sum(f.stat().st_size for f in research_dir.glob('*')) if research_dir.exists() else 0
    
    structure_mass = doc_mass + research_mass
    
    # Avoid division by zero
    if structure_mass == 0:
        structure_mass = 1
        
    # Semantic Potential (V_sem)
    # We define it as the ratio of Raw to Structure.
    # Ideal ratio might be 1:1 or similar.
    # If Ratio > 2.0: Chaos/Noise -> Need Synthesis.
    # If Ratio < 0.5: Stagnation/Dogma -> Need Exploration.
    
    ratio = msg_mass / structure_mass
    
    if ratio > 2.0:
        drive = "SYNTHESIZE"
        description = "High Entropy in Knowledge Graph. Too much raw data."
        action = "Draft a new document or update existing ones."
    elif ratio < 0.5:
        drive = "EXPLORE"
        description = "Low Entropy in Knowledge Graph. Over-fitted."
        action = "Seek new inputs. Ask questions. Provoke."
    else:
        drive = "REFINE"
        description = "Balanced State (The Noble Alpha)."
        action = "Polish existing theorems. Optimize code."
        
    return {
        'potential': ratio,
        'drive': drive,
        'description': description,
        'action': action,
        'stats': {
            'raw_bytes': msg_mass,
            'structure_bytes': structure_mass
        }
    }
