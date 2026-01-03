#!/usr/bin/env python3
"""Test keyword extraction LLM call."""
import requests
import json

prompt = """Extract 5-10 keywords from this file understanding:

FILE: wake.py
UNDERSTANDING:
[Insight] Wake is a toll booth: you cannot think until you know what you know is current
[Purpose] Restore full cognitive state: goals, intentions, messages, debt - block work until sync
[Design_Decision] Two-enclave architecture: shared (semantic memory) + private (goals, intentions)

Return ONLY a JSON array of lowercase keywords:
["keyword1", "keyword2", ...]"""

print("Sending to Ollama...")
try:
    response = requests.post(
        'http://localhost:11434/api/generate',
        json={
            'model': 'qwen2.5:7b',
            'prompt': prompt,
            'stream': False,
            'format': 'json',
            'options': {'temperature': 0.2}
        },
        timeout=60
    )
    print(f'Status: {response.status_code}')
    result = response.json()
    raw = result.get('response', 'NO RESPONSE')
    print(f'Raw response: {raw}')
    
    parsed = json.loads(raw)
    print(f'Parsed: {parsed}')
except Exception as e:
    print(f'Error: {e}')
