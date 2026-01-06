def action(ctx):
    inbox = ctx.get('final_inbox', [])
    summary = []
    for msg in inbox:
        sender = msg.get('sender', 'unknown')
        ts = msg.get('timestamp', '?')
        content = msg.get('content', '')[:50]
        summary.append(f'[{ts}] {sender}: {content}...')
    
    if not summary: return 'Inbox empty'
    return '\n'.join(summary)