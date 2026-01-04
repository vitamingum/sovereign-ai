import json

# Simulated DeepSeek output
action_code = '''import json
def action(ctx):
    knowledge = ctx.get('__knowledge__', [])
    if not knowledge:
        return {'error': 'No knowledge provided'}
    data = json.loads(knowledge[0])
    theme = data.get('theme')
    agent_id = data.get('agent_id')
    return {'theme': theme, 'agent_id': agent_id}
'''

test_code = '''def test(ctx, result):
    required_keys = ['theme', 'agent_id']
    if not all(key in result for key in required_keys):
        return False
    if result['theme'] is None or result['agent_id'] is None:
        return False
    return True
'''

# Execute action
exec(action_code)
ctx = {'__knowledge__': ['{"theme": "test-junk", "agent_id": "opus"}']}
result = action(ctx)
print(f'Action result: {result}')

# Execute test
exec(test_code)
passed = test(ctx, result)
print(f'Test passed: {passed}')
