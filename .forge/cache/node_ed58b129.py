def action(ctx):
    import json
    from enclave.config import get_agent_or_raise

    try:
        passphrase = ctx.get('passphrase')
        if not passphrase:
            raise ValueError("Passphrase not found")
    except KeyError:
        knowledge = ctx.get('__knowledge__', [])
        for item in knowledge:
            data = json.loads(item)
            if 'passphrase' in data:
                passphrase = data['passphrase']
                break
        else:
            raise ValueError("Passphrase not found")

    return {'error': False, 'message': 'Passphrase found'}