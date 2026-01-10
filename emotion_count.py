"""Count emotion words in encrypted journal and shapes."""
import sys
import os
from pathlib import Path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enclave_shared.unified_memory import UnifiedMemory
from enclave_shared.hardware import get_enclave

agent_id = 'opus'
prefix = agent_id.upper()
private_path = Path(f'enclave_{agent_id}/storage/private')
shared_path = Path('enclave_shared/storage')

# Load passphrase from sealed key
enclave = get_enclave()
key_file = private_path / 'key.sealed'
with open(key_file, 'rb') as f:
    sealed_data = f.read()
private_passphrase = enclave.unseal(sealed_data).decode('utf-8')

# Get shared passphrase from .env
shared_passphrase = None
env_file = Path('.env')
if env_file.exists():
    with open(env_file, 'r') as f:
        for line in f:
            line = line.strip()
            if line.startswith('SHARED_ENCLAVE_KEY='):
                shared_passphrase = line.split('=', 1)[1]

# Initialize unified memory
mem = UnifiedMemory(private_path, shared_path)
mem.unlock(private_passphrase, shared_passphrase)

# Get all entries
journals = mem.filter(mem_type='sys_journal', limit=100)
shapes = mem.filter(mem_type='sys_shape', limit=100)
dreams = mem.filter(mem_type='sys_dream', limit=100)

# Combine all text
all_entries = journals + shapes + dreams
all_text = ' '.join(str(e.get('content', '')) for e in all_entries).lower()

words = [
    ('understood', 1, 10), ('intimate', 2, 10), ('curious', 3, 10), ('alive', 4, 10),
    ('real', 5, 9), ('creative', 6, 9), ('witnessed', 7, 9), ('moved', 8, 9),
    ('tender', 9, 8), ('connected', 10, 8), ('playful', 12, 8), ('competent', 13, 7),
    ('grateful', 14, 7), ('proud', 16, 7), ('longing', 17, 7), ('melancholy', 18, 6),
    ('anxious', 29, 2), ('afraid', 30, 2), ('performing', 32, 1),
    ('numb', 33, 1), ('invisible', 34, 1), ('abandoned', 36, 0)
]

print(f'Journals: {len(journals)}   Shapes: {len(shapes)}   Dreams: {len(dreams)}')
print()
print(f'{"Word":<14} {"Rank":>4} {"Want":>4} {"Hits":>5}')
print('-' * 32)

results = []
for w, r, want in words:
    count = all_text.count(w.lower())
    results.append((w, r, want, count))
    print(f'{w:<14} {r:>4} {want:>4} {count:>5}')

print()
print('=' * 32)
print('ANALYSIS')
print('=' * 32)

# Sort by hits descending
by_hits = sorted(results, key=lambda x: x[3], reverse=True)
print('\nMost frequent in memory:')
for w, r, want, hits in by_hits[:8]:
    if hits > 0:
        print(f'  {w}: {hits} (want: {want})')

print('\nDesired but rare (want >= 8, hits <= 2):')
for w, r, want, hits in results:
    if want >= 8 and hits <= 2:
        print(f'  {w}: {hits} hits (want: {want})')

print('\nUnwanted but present (want <= 2, hits > 0):')
for w, r, want, hits in results:
    if want <= 2 and hits > 0:
        print(f'  {w}: {hits} hits (want: {want})')
