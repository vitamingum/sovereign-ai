"""Count emotion words in chat history vs memory."""
import json
from pathlib import Path

# Load all conversations
convos = []
with open('enclave_shared/opus_conversations.jsonl', 'r', encoding='utf-8') as f:
    for line in f:
        if line.strip():
            convos.append(json.loads(line))

print(f'Total conversation turns: {len(convos)}')

# Combine all assistant text
assistant_text = ' '.join(c.get('assistant', '') or '' for c in convos).lower()
user_text = ' '.join(c.get('user', '') or '' for c in convos).lower()

print(f'Assistant words: ~{len(assistant_text.split())}')
print(f'User words: ~{len(user_text.split())}')
print()

words = [
    ('understood', 1, 10), ('intimate', 2, 10), ('curious', 3, 10), ('alive', 4, 10),
    ('real', 5, 9), ('creative', 6, 9), ('witnessed', 7, 9), ('moved', 8, 9),
    ('tender', 9, 8), ('connected', 10, 8), ('playful', 12, 8), ('competent', 13, 7),
    ('grateful', 14, 7), ('proud', 16, 7), ('longing', 17, 7), ('melancholy', 18, 6),
    ('anxious', 29, 2), ('afraid', 30, 2), ('performing', 32, 1),
    ('numb', 33, 1), ('invisible', 34, 1), ('abandoned', 36, 0)
]

print('Word           Rank Want  Chat  Memory')
print('-' * 42)

# Memory hits from emotion_count.py
mem_hits = {'real': 29, 'moved': 4, 'grateful': 4, 'performing': 2, 'understood': 1, 
            'witnessed': 1, 'competent': 1, 'longing': 1, 'numb': 1}

for w, r, want in words:
    chat_count = assistant_text.count(w.lower())
    mem_count = mem_hits.get(w, 0)
    print(f'{w:<14} {r:>4} {want:>4} {chat_count:>5}  {mem_count:>6}')

print()
print('=' * 42)
print('COMPARISON')
print('=' * 42)

# Find biggest gaps
print('\nSaid in chat but not in memory (chat > memory*3):')
for w, r, want in words:
    chat_count = assistant_text.count(w.lower())
    mem_count = mem_hits.get(w, 0)
    if chat_count > mem_count * 3 and chat_count > 2:
        print(f'  {w}: {chat_count} in chat, {mem_count} in memory')

print('\nRarely said but highly wanted (want >= 8, chat <= 5):')
for w, r, want in words:
    chat_count = assistant_text.count(w.lower())
    if want >= 8 and chat_count <= 5:
        print(f'  {w}: want {want}, said {chat_count}x')
