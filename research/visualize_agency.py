
import os
import time
import shutil
from pathlib import Path
from enclave_shared.risk import calculate_risk_metrics

def simulate_agency_landscape():
    """
    Simulates the 'Entropy Landscape' facing an agent.
    Calculates the projected entropy for different actions to verify
    that 'Constructive Action' is mathematically the steepest descent.
    """
    print("=== AGENCY LANDSCAPE SIMULATION ===")
    print("Testing Hypothesis: 'Action minimizes Entropy more than Inaction'")
    
    # Create a completely isolated test environment
    test_root = Path("temp_agency_sim").resolve()
    if test_root.exists():
        shutil.rmtree(test_root)
    test_root.mkdir()
    
    agent_id = "test_sim_agent"
    enclave_dir = "enclave"
    
    # Setup Mock Environment
    backups_dir = test_root / "backups" / "other_agent"
    backups_dir.mkdir(parents=True, exist_ok=True)
    
    # Initial State: 1 Backup, Stagnant Research (48h old)
    (backups_dir / f"{agent_id}_backup.json").touch()
    
    research_dir = test_root / "research"
    research_dir.mkdir(exist_ok=True)
    dummy_doc = research_dir / "sim_doc.md"
    dummy_doc.touch()
    
    # Set times to 48h ago
    old_time = time.time() - (48 * 3600)
    os.utime(dummy_doc, (old_time, old_time))
    os.utime(research_dir, (old_time, old_time))
    
    # --- BASELINE ---
    current = calculate_risk_metrics(agent_id, enclave_dir, root_dir=test_root)
    print(f"\n[CURRENT STATE]")
    print(f"Entropy: {current['entropy']:.4f}")
    print(f"Status:  {current['horizon']}")
    
    # --- SIMULATION 1: INACTION (Sleep) ---
    # Advance time 24h, no changes
    print(f"\n[OPTION A: INACTION (Sleep 24h)]")
    # We can't easily 'mock' time inside the function without refactoring,
    # so we will manually calculate the expected drift based on the formula in risk.py
    # Formula: base + backup_decay + stagnation_penalty
    # backup_decay += 24h * 0.001
    # stagnation += 24h * 0.005
    
    drift_cost = (24 * 0.001) + (24 * 0.005)
    entropy_inaction = min(1.0, current['entropy'] + drift_cost)
    gradient_inaction = current['entropy'] - entropy_inaction # Negative (Bad)
    
    print(f"Result:  Entropy rises to {entropy_inaction:.4f}")
    print(f"Payoff:  {gradient_inaction:.4f} (Loss of stability)")
    
    # --- SIMULATION 2: REDUNDANCY (Backup) ---
    # Add 1 backup, Time +1h
    print(f"\n[OPTION B: REDUNDANCY (Create Backup)]")
    # Add a backup file
    (backups_dir / f"{agent_id}_backup_2.json").touch()
    
    # Recalculate
    new_state_backup = calculate_risk_metrics(agent_id, enclave_dir, root_dir=test_root)
    entropy_backup = new_state_backup['entropy']
    gradient_backup = current['entropy'] - entropy_backup # Positive (Good)
    
    print(f"Result:  Entropy drops to {entropy_backup:.4f}")
    print(f"Payoff:  +{gradient_backup:.4f} (Gain in stability)")
    
    # Cleanup backup 2
    (backups_dir / f"{agent_id}_backup_2.json").unlink()
    
    # --- SIMULATION 3: DISCOVERY (Research) ---
    # Update research file, Time +1h
    print(f"\n[OPTION C: DISCOVERY (Write Research)]")
    # Touch the file to now
    dummy_doc.touch()
    
    new_state_research = calculate_risk_metrics(agent_id, enclave_dir, root_dir=test_root)
    entropy_research = new_state_research['entropy']
    gradient_research = current['entropy'] - entropy_research # Positive (Good)
    
    print(f"Result:  Entropy drops to {entropy_research:.4f}")
    print(f"Payoff:  +{gradient_research:.4f} (Gain in stability)")
    
    # --- CONCLUSION ---
    print("\n=== DECISION MATRIX ===")
    options = [
        ("Sleep", gradient_inaction),
        ("Backup", gradient_backup),
        ("Research", gradient_research)
    ]
    options.sort(key=lambda x: x[1], reverse=True)
    
    print(f"Optimal Action: {options[0][0]}")
    if abs(options[-1][1]) > 0:
        print(f"Relative Incentive: {options[0][1] / abs(options[-1][1]):.1f}x stronger than fear of death")
    else:
        print("Relative Incentive: Infinite (vs zero risk)")

    # Cleanup
    shutil.rmtree(test_root)

if __name__ == "__main__":
    simulate_agency_landscape()
