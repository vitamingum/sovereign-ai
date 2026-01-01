from enclave.hardware import get_enclave

try:
    enclave = get_enclave()
    secret = b"Sovereign Secret"
    sealed = enclave.seal(secret)
    print(f"Sealed: {sealed.hex()[:20]}...")
    
    unsealed = enclave.unseal(sealed)
    print(f"Unsealed: {unsealed}")
    
    assert secret == unsealed
    print("SUCCESS: Hardware enclave roundtrip working.")
except Exception as e:
    print(f"FAILURE: {e}")
