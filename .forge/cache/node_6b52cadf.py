import json

def action(ctx):
    data = json.loads(ctx.get('__knowledge__', [])[0])
    theme = data.get('theme')
    
    # Load credentials and unlock identity
    agent_id = data.get('agent_id')
    agent = get_agent_or_raise(agent_id)
    passphrase = os.environ[agent.env_key_var]
    identity = SovereignIdentity(agent.private_enclave)
    if not identity.unlock(passphrase):
        raise Exception("Failed to unlock identity")
    
    # Use semantic memory
    enclave_path = agent.shared_enclave
    memory = SemanticMemory(enclave_path)
    if not memory.unlock(passphrase):
        raise Exception("Failed to unlock memory")
    
    # Parse and process the theme
    deleted_count = memory.forget(theme=theme)
    
    return {"deleted_count": deleted_count}