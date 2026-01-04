def action(ctx):
    import json
    import os
    from pathlib import Path
    from enclave.config import get_agent_or_raise
    from enclave.semantic_memory import SemanticMemory
    
    agent_id = ctx.get('agent_id')
    if not agent_id:
        knowledge = ctx.get('__knowledge__', [])
        for item in knowledge:
            data = json.loads(item)
            if 'agent_id' in data:
                agent_id = data['agent_id']
                break
    
    if not agent_id:
        raise ValueError("Agent ID is required")
    
    agent = get_agent_or_raise(agent_id)
    return {"enclave_dir": agent.shared_enclave}