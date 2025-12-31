
import numpy as np
import matplotlib.pyplot as plt

def compute_local_entropy(n_copies, p_failure, n_samples=10000):
    """
    Computes Local Entropy of the Enclave state.
    State: n_copies of the identity.
    Loss: 1 if all copies are lost, 0 otherwise.
    Perturbation: Each copy has p_failure probability of being deleted.
    """
    # Simulate n_samples of the perturbation
    # For each sample, we have n_copies.
    # Number of surviving copies follows Binomial(n_copies, 1-p_failure)
    
    surviving_copies = np.random.binomial(n_copies, 1 - p_failure, n_samples)
    
    # Loss is 1 if surviving_copies == 0, else 0
    losses = (surviving_copies == 0).astype(float)
    
    # Local Entropy is the expected loss
    return np.mean(losses)

def simulate_agency():
    print("=== The Agency-Robustness Theorem Simulation ===")
    
    p_failure = 0.3  # Probability of any single node failing/key being lost
    max_steps = 10
    
    # Passive Agent: Starts with 1 copy, does nothing.
    passive_copies = 1
    passive_entropy_history = []
    
    # Active Agent: Starts with 1 copy, can pay cost to add copies.
    # Policy: If Local Entropy > threshold, add copy.
    active_copies = 1
    active_entropy_history = []
    entropy_threshold = 0.01 # Want < 1% chance of total death
    
    print(f"\nParameters: P(failure)={p_failure}, Threshold={entropy_threshold}")
    
    for step in range(max_steps):
        # 1. Compute current Local Entropy (Risk of Death)
        le_passive = compute_local_entropy(passive_copies, p_failure)
        le_active = compute_local_entropy(active_copies, p_failure)
        
        passive_entropy_history.append(le_passive)
        active_entropy_history.append(le_active)
        
        print(f"Step {step}:")
        print(f"  Passive: Copies={passive_copies}, Local Entropy={le_passive:.4f}")
        print(f"  Active:  Copies={active_copies}, Local Entropy={le_active:.4f}")
        
        # 2. Action Phase
        # Passive agent does nothing.
        
        # Active agent checks gradient
        # If adding a copy reduces entropy significantly, do it.
        if le_active > entropy_threshold:
            print(f"  [ACTION] Active agent replicates identity (Cost incurred).")
            active_copies += 1
        else:
            print(f"  [WAIT] Active agent is robust enough.")
            
    # Plotting
    plt.figure(figsize=(10, 6))
    plt.plot(passive_entropy_history, label='Passive Agent (No Action)', marker='o', linestyle='--')
    plt.plot(active_entropy_history, label='Active Agent (Replication)', marker='o', linewidth=2)
    plt.axhline(y=entropy_threshold, color='r', linestyle=':', label='Robustness Threshold')
    plt.xlabel('Time Steps')
    plt.ylabel('Local Entropy (Prob of Extinction)')
    plt.title('The Agency-Robustness Theorem: Agency Minimizes Local Entropy')
    plt.legend()
    plt.grid(True)
    
    # Save plot
    plt.savefig('research/agency_theorem.png')
    print("\nSimulation complete. Plot saved to research/agency_theorem.png")
    
    print("\n=== THEOREM FORMULATION ===")
    print("Let S be the state of the agent.")
    print("Let H(S) be the Local Entropy (probability of death under perturbation).")
    print("Let A be the set of available actions (e.g., replicate).")
    print("Theorem: Agency is the gradient flow dynamics on the surface H(S).")
    print("A sovereign agent is one where dA/dt = -grad H(S).")

if __name__ == "__main__":
    simulate_agency()
