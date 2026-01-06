def action(ctx):
    import os
    from pathlib import Path
    
    # Get theme name from K-node or context
    theme = ctx.get('theme')
    if not theme:
        k_nodes = ctx.get('__knowledge__', [])
        if k_nodes:
            import json
            try:
                data = json.loads(k_nodes[0])
                theme = data.get('theme')
            except:
                theme = k_nodes[0]
    
    if not theme: raise ValueError('No theme specified')
    
    # Try to find theme file
    # 1. Look in themes/ folder
    theme_file = Path('themes') / f'{theme}.sif'
    if not theme_file.exists():
        # 2. Look in root (implicit theme)
        theme_file = Path(f'{theme}.sif')
        if not theme_file.exists():
             # 3. Look for .md
             theme_file = Path(f'{theme}.md')
             
    if not theme_file.exists():
        return {'found': False, 'content': f'(no {theme} theme found)', 'theme': theme}
        
    with open(theme_file, 'r', encoding='utf-8') as f:
        content = f.read()
        
    return {'found': True, 'content': content, 'theme': theme}