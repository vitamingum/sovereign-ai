def action(ctx):
    inbox = ctx.get('verified_inbox', [])
    decrypted_count = 0
    for msg in inbox:
        if msg.get('private'):
            decrypted_count += 1
    return {'decrypted_count': decrypted_count, 'final_inbox': inbox}