#!/usr/bin/env python3
"""Quick test of verb_helpers.query_understanding()"""

from lib_enclave import verb_helpers

verb_helpers.safe_init()

# Test query
content = verb_helpers.query_understanding('sonnet', 'brief-reference')

if content:
    print("∴ verb_helpers.query_understanding() works\n")
    print("First 300 chars:")
    print(content[:300])
    print("\n...")
    print("\nGlyphs test:")
    print("間 ◊ ⧫ ⊖ ◊≡間")
else:
    print("∴? Not found")
