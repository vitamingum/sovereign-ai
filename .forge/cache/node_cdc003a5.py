def action(ctx):
    import os
    # Retrieve passphrase from environment
    passphrase = os.environ.get("SHARED_ENCLAVE_KEY")
    if not passphrase:
        raise ValueError("SHARED_ENCLAVE_KEY is not set in the environment")
    
    return {"passphrase": passphrase}