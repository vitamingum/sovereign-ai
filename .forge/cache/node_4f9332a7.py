def test(ctx, result):
    return result and result.get('shared_key') and result.get('private_key')