def action(ctx):
    import json
    
    agent_id = ctx.get('agent_id', 'gemini')
    files = ctx.get('files', [])
    
    my_msgs = []
    for fpath in files:
        try:
            with open(fpath, 'r') as f:
                data = json.load(f)
                if data.get('recipient') == agent_id:
                    my_msgs.append(data)
        except Exception as e:
            print(f'Error reading {fpath}: {e}')
            
    return {'inbox': my_msgs}