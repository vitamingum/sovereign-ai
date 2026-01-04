def action(ctx):
    # Real Implementation
    import json
    from enclave.config import get_agent_or_raise
    
    # Simulate loading from K-node
    k_nodes = ctx.get('__knowledge__', [])
    if not k_nodes: return None
    
    # Parse K-node to get agent_id
    data = json.loads(k_nodes[0])
    agent_id = data.get('agent_id')
    
    # Load real config
    agent = get_agent_or_raise(agent_id)
    print(f'Loaded REAL config for {agent.name}')
    return {'agent_id': agent.id, 'agent_obj': agent}