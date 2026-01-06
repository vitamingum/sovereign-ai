def action(ctx):
    import os
    import glob
    from pathlib import Path
    
    messages_dir = Path('messages')
    if not messages_dir.exists():
        messages_dir.mkdir()
    
    files = glob.glob(str(messages_dir / '*.json'))
    ctx['message_files'] = files
    return {'count': len(files), 'files': files}