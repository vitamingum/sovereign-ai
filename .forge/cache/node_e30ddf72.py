def action(ctx):
    # Real Implementation
    import os
    import sys
    from pathlib import Path
    from enclave.hardware import get_enclave
    
    config = ctx.get('load')
    if not config: raise ValueError('No config fed from previous node')
    agent = config['agent_obj']
    
    print(f'Loading REAL keys for {agent.name}...')
    
    # 1. Shared Key
    shared_passphrase = os.environ.get('SHARED_ENCLAVE_KEY')
    if not shared_passphrase:
        env_file = Path('.env')
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    if line.startswith('SHARED_ENCLAVE_KEY='):
                        shared_passphrase = line.split('=', 1)[1].strip()
    
    # 2. Private Key (Hardware Enclave)
    private_passphrase = None
    key_file = Path(agent.private_enclave) / 'storage' / 'private' / 'key.sealed'
    if key_file.exists():
        try:
            with open(key_file, 'rb') as f: sealed_data = f.read()
            enclave = get_enclave()
            private_passphrase = enclave.unseal(sealed_data).decode('utf-8')
            print('  -> Unsealed key from Hardware Enclave')
        except Exception as e:
            print(f'  -> Failed to unseal: {e}')
            
    if not private_passphrase:
        # Fallback to env
        private_passphrase = os.environ.get(f'{agent.env_prefix}_KEY')
        
    return {'shared_key': shared_passphrase, 'private_key': private_passphrase, 'shared_dir': agent.shared_enclave, 'private_dir': agent.private_enclave}