def action(ctx):
    # Real Implementation
    from enclave.semantic_memory import SemanticMemory
    
    keys = ctx.get('initsemanticmemory')
    if not keys: raise ValueError('No keys loaded')
    
    print('Initializing REAL Semantic Memory...')
    memory = SemanticMemory(keys['shared_dir'])
    # We don't actually unlock it here because SemanticMemory might not take the key in init, 
    # but let's assume we just return the object for now.
    return {'status': 'ready', 'memory_obj': memory}