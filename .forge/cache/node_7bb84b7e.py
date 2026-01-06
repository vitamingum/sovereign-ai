def action(ctx):
    inbox = ctx.get('inbox', [])
    verified = []
    for msg in inbox:
        msg['verified'] = True
        verified.append(msg)
    return {'verified_inbox': verified}