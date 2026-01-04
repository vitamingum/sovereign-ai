import sys
import os

# Set up the same args
sys.argv = ['remember.py', 'gemini', '--theme', 'logic-parity-testing', 
            "@G test gemini 2026-01-04; N S 'Test 1'; N I 'Test 2'; N D 'Test 3'; N G 'Test 4'; E _1 relates _2; E _3 relates _4"]

from pathlib import Path
from enclave.sif_parser import SIFParser

# Get args
theme_idx = sys.argv.index('--theme')
agent_id = sys.argv[1]
topic = sys.argv[theme_idx + 1]
sif_arg = sys.argv[theme_idx + 2]

sif_content = SIFParser.to_autocount(sif_arg.strip())
print(f"Agent: {agent_id}")
print(f"Topic: {topic}")
print(f"SIF:\n{sif_content}")

# Now import the actual function
from remember import load_passphrase, store_theme, evaluate_theme_depth

# Validate depth
is_deep, issues = evaluate_theme_depth(sif_content)
print(f"\nDepth check: is_deep={is_deep}, issues={issues}")

if is_deep:
    result = store_theme(agent_id, topic, sif_content)
    print(f"\nStore result: {result}")
