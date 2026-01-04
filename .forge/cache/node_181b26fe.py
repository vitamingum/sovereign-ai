def logic(ctx):
    return 'passphrase' in ctx.get('__knowledge__', [])