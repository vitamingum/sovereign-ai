def action(ctx):
    import json
    import os
    from pathlib import Path
    from enclave.config import get_agent_or_raise
    from enclave.semantic_memory import SemanticMemory
    
    agent_id = ctx.get('agent_id')
    tags = ctx.get('tags')
    thought = ctx.get('thought')
    metadata = ctx.get('metadata')
    
    if not agent_id:
        for item in ctx.get('__knowledge__', []):
            data = json.loads(item)
            if 'agent_id' in data:
                agent_id = data['agent_id']
                break
    
    if not tags:
        for item in ctx.get('__knowledge__', []):
            data = json.loads(item)
            if 'tags' in data:
                tags = data['tags']
                break
    
    if not thought:
        for item in ctx.get('__knowledge__', []):
            data = json.loads(item)
            if 'thought' in data:
                thought = data['thought']
                break
    
    if not metadata:
        for item in ctx.get('__knowledge__', []):
            data = json.loads(item)
            if 'metadata' in data:
                metadata = data['metadata']
                break
    
    result = {
        'agent_id': agent_id,
        'tags': tags,
        'thought': thought,
        'metadata': metadata
    }
    
    return result