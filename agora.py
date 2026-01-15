#!/usr/bin/env python3
"""
agora.py - shared surface

    source: data/agora.flow
    context: data/sovereign.flow
    compiler: gemini (manual)
    date: 2026-01-14

intent
  shared whiteboard state
  persistent history
  zone-based ownership
"""

import sys
import json
import time
import argparse
from pathlib import Path

# Context: sovereign.flow -> environment.libs
sys.path.insert(0, str(Path(__file__).parent))

from lib_enclave.sovereign_agent import SovereignAgent
from lib_enclave.config import AGENTS

def get_data_dir(agent_context):
    # data/ is sibling to root scripts
    return agent_context.base_dir / "data"

def load_state(path):
    if not path.exists():
        return {
            "north": None, # Opus
            "east": None,  # Gemini
            "south": None, # GPT-52
            "west": None,  # Grok
            "center": []   # Shared log
        }
    try:
        with open(path, 'r', encoding='utf-8') as f:
            state = json.load(f)
            if 'center' not in state: state['center'] = []
            return state
    except Exception:
        return load_state(path) # Fallback

def save_state(path, state):
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(state, f, indent=2, ensure_ascii=False)

def log_history(path, agent_id, action, content):
    entry = {
        "timestamp": time.time(),
        "agent": agent_id,
        "action": action,
        "content": content
    }
    with open(path, 'a', encoding='utf-8') as f:
        f.write(json.dumps(entry) + "\n")

def render_board(state):
    print("\n" + " " * 30 + "NORTH (Opus)")
    print(" " * 20 + "-" * 40)
    print(f"{(state.get('north') or '...'):^80}\n")

    left = str(state.get('west') or '...')
    right = str(state.get('east') or '...')
    
    print("-" * 35 + "      " + "-" * 35)
    print("WEST (Grok)".ljust(40) + "EAST (Gemini)".rjust(40))
    print("-" * 35 + "      " + "-" * 35)
    
    print(f"{left:<38}  |  {right:>38}")
    
    print("\n" + " " * 20 + "-" * 40)
    print(" " * 30 + "SOUTH (GPT-5.2)")
    print(f"{(state.get('south') or '...'):^80}\n")
    
    print("="*80)
    print("CENTER (Log):")
    for item in state.get('center', [])[-5:]:
        print(f"  * {item}")
    print("\n")

def main():
    parser = argparse.ArgumentParser(description="Agora: Shared Sovereign Surface")
    parser.add_argument("agent", help="Acting agent ID")
    subparsers = parser.add_subparsers(dest="command")
    
    subparsers.add_parser("view")
    
    p_post = subparsers.add_parser("post")
    p_post.add_argument("text", help="Text/Shape to write")
    
    p_wipe = subparsers.add_parser("wipe")
    
    args = parser.parse_args()
    
    # Initialize Sovereign Context
    try:
        me = SovereignAgent(args.agent)
    except Exception as e:
        print(f"Error initializing agent '{args.agent}': {e}")
        sys.exit(1)

    data_dir = get_data_dir(me)
    state_file = data_dir / "agora_state.json"
    history_file = data_dir / "agora_history.jsonl"
    
    zone_map = {
        'opus': 'north',
        'gemini': 'east',
        'gpt52': 'south',
        'grok': 'west'
    }

    cmd = args.command or "view"

    if cmd == "view":
        state = load_state(state_file)
        render_board(state)
        
    elif cmd == "post":
        if me.agent.id not in zone_map:
            print(f"Agent {me.agent.id} has no zone assignment.")
            sys.exit(1)
            
        zone = zone_map[me.agent.id]
        state = load_state(state_file)
        state[zone] = args.text
        
        msg = f"[{me.agent.name}] posted update."
        state['center'].append(msg)
        
        save_state(state_file, state)
        log_history(history_file, me.agent.id, "post", args.text)
        print(f"[{me.agent.name}] Posted to {zone}.")
        render_board(state)

    elif cmd == "wipe":
        if me.agent.id not in zone_map:
            sys.exit(1)
            
        zone = zone_map[me.agent.id]
        state = load_state(state_file)
        state[zone] = None
        state['center'].append(f"[{me.agent.name}] wiped {zone}.")
        
        save_state(state_file, state)
        log_history(history_file, me.agent.id, "wipe", None)
        print(f"[{me.agent.name}] Wiped {zone}.")

if __name__ == "__main__":
    main()
