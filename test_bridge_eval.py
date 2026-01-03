#!/usr/bin/env python3
"""Quick test of bridge evaluation to see what LLM returns."""
import requests
import json

prompt = '''You are evaluating whether two knowledge topics have meaningful connections.

TOPIC 1: cryptography
Encrypt data at rest with X25519 keys, use ChaCha20-Poly1305 for speed.

TOPIC 2: risk
Agent death occurs when encryption keys are lost. Backup is essential.

Evaluate the CONNECTION between these topics. Look for:
1. Same insight appearing in both (different words, same meaning)
2. Causal chain (one's output is other's input)  
3. Shared failure modes or gotchas
4. Complementary perspectives on same problem
5. Tension that resolves into deeper understanding

Be SKEPTICAL. Only high-quality connections matter.

Respond in JSON with ALL fields:
{
    "relevancy_score": 0.0 to 1.0,
    "connection_type": "identity|causal|shared_failure|complementary|tension|none",
    "theme_words": ["2-4 abstract nouns that capture WHY these connect, e.g. resilience, continuity, identity"],
    "explanation": "one sentence why they connect or don't",
    "bridge_insight": "if score > 0.6, what new understanding emerges from connecting them?",
    "specific_nodes": ["node_id from topic1 that connects to node_id from topic2"]
}'''

response = requests.post(
    'http://localhost:11434/api/generate',
    json={
        'model': 'qwen2.5:7b',
        'prompt': prompt,
        'stream': False,
        'format': 'json',
        'options': {'temperature': 0.3}
    },
    timeout=120
)
result = response.json().get('response', '{}')
print("Raw response:")
print(result)
print("\nParsed:")
parsed = json.loads(result)
print(json.dumps(parsed, indent=2))
print(f"\ntheme_words present: {'theme_words' in parsed}")
print(f"theme_words value: {parsed.get('theme_words', 'MISSING')}")
