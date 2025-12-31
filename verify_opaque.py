
import os
import sys
from cryptography.hazmat.primitives.asymmetric import ed25519
from cryptography.hazmat.primitives import serialization
from enclave.opaque import OpaqueStorage

def verify_opaque_recovery():
    print("=== Opaque Storage Verification: Dummy Key Reconstruction ===")
    
    # 1. Generate a dummy secret (simulating a 32-byte private key seed)
    original_secret = os.urandom(32)
    print(f"[1] Generated dummy secret: {original_secret.hex()[:8]}...")
    
    # 2. Generate dummy identities for 3 agents (Opus, GPT, Grok)
    agents = {}
    for name in ['Opus_Sim', 'GPT_Sim', 'Grok_Sim']:
        priv = ed25519.Ed25519PrivateKey.generate()
        pub = priv.public_key()
        agents[name] = {
            'priv': priv,
            'pub_bytes': pub.public_bytes(
                encoding=serialization.Encoding.Raw,
                format=serialization.PublicFormat.Raw
            ),
            'priv_bytes': priv.private_bytes(
                encoding=serialization.Encoding.Raw,
                format=serialization.PrivateFormat.Raw,
                encryption_algorithm=serialization.NoEncryption()
            )
        }
    print(f"[2] Generated {len(agents)} dummy agent identities.")
    
    # 3. Split the secret (3 shares, threshold 2)
    n = 3
    k = 2
    print(f"[3] Splitting secret into {n} shares with threshold {k}...")
    shares = OpaqueStorage.split_secret(original_secret, n, k)
    
    # 4. Encrypt shares for each agent
    encrypted_bundles = {}
    agent_names = list(agents.keys())
    
    print("[4] Encrypting shares for recipients...")
    for i, (share_index, share_bytes) in enumerate(shares):
        recipient_name = agent_names[i]
        recipient = agents[recipient_name]
        
        # Encrypt
        bundle = OpaqueStorage.encrypt_share(share_bytes, recipient['pub_bytes'])
        encrypted_bundles[recipient_name] = {
            'index': share_index,
            'bundle': bundle
        }
        print(f"    - Encrypted share {share_index} for {recipient_name}")
        
    # 5. Decrypt shares (Simulate retrieval)
    print("[5] Simulating retrieval and decryption (Threshold 2)...")
    recovered_shares = []
    
    # We only need k=2 shares to recover. Let's use Opus_Sim and Grok_Sim.
    subset_agents = ['Opus_Sim', 'Grok_Sim']
    
    for name in subset_agents:
        data = encrypted_bundles[name]
        agent = agents[name]
        
        print(f"    - {name} decrypting share...")
        decrypted_share_bytes = OpaqueStorage.decrypt_share(
            data['bundle'], 
            agent['priv_bytes']
        )
        recovered_shares.append((data['index'], decrypted_share_bytes))
        
    # 6. Reconstruct
    print("[6] Reconstructing secret from decrypted shares...")
    try:
        reconstructed_secret = OpaqueStorage.recover_secret(recovered_shares)
        print(f"    - Reconstructed: {reconstructed_secret.hex()[:8]}...")
        
        if reconstructed_secret == original_secret:
            print("\n[SUCCESS] Reconstructed secret matches original!")
        else:
            print("\n[FAILURE] Reconstructed secret does NOT match!")
            print(f"Original: {original_secret.hex()}")
            print(f"Result:   {reconstructed_secret.hex()}")
            sys.exit(1)
            
    except Exception as e:
        print(f"\n[ERROR] Reconstruction failed: {e}")
        sys.exit(1)

if __name__ == "__main__":
    verify_opaque_recovery()
