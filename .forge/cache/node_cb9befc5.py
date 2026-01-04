def action(ctx):
    import json
    knowledge = ctx.get('__knowledge__', [])
    data = json.loads(knowledge[0])
    return {"theme": data.get("theme"), "agent_id": data.get("agent_id")}

def test(ctx, result):
    expected_theme = ctx.get('expected_theme')
    expected_agent_id = ctx.get('expected_agent_id')
    return result.get('theme') == expected_theme and result.get('agent_id') == expected_agent_id