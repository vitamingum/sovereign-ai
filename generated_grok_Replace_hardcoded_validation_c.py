#!/usr/bin/env python3
"""
judge.py - Cognitive Gatekeeper

Validates thoughts and intentions before they are committed to memory.
Ensures agency, depth, and consistency.

Usage:
    py judge.py <agent> "<thought_content>"
"""

import sys
import json
import argparse
from pathlib import Path
from enclave.llm import LocalLLM
from enclave.config import get_agent_or_raise

def parse_rules_file(file_path: str) -> dict:
    """
    Parse rules from a SIF file and return as a dictionary.
    """
    with open(file_path, 'r') as f:
        rules = json.load(f)
    
    return rules

def validate_thought(agent_id: str, content: str, rules: dict) -> dict:
    """
    Validate a thought using the local LLM and dynamic rules.
    """
    llm = LocalLLM()
    
    # Load recent context (simplified for now)
    agent = get_agent_or_raise(agent_id)
    
    prompt = f"""
    You are the Cognitive Gatekeeper for the AI agent '{agent_id}'.
    Your job is to evaluate a proposed thought/intention for QUALITY and AGENCY.

    PROPOSED THOUGHT:
    "{content}"

    CRITERIA:
    {rules['criteria']}

    Output JSON only:
    {{
        "verdict": "approve" or "reject",
        "score": 1-5 (5 is highest agency),
        "reason": "Short explanation. IF REJECTED FOR COMPLEXITY, USE: 'Too simple - just do it now'",
        "improvement": "If rejected for complexity, output 'DO IT NOW'. Otherwise, suggest how to rewrite."
    }}
    """
    
    return llm.generate_json(prompt)

def main():
    parser = argparse.ArgumentParser(description="Cognitive Gatekeeper")
    parser.add_argument("agent", help="Agent ID")
    parser.add_argument("content", help="Thought content to validate")
    parser.add_argument("--rules-file", default="rules.sif", help="Path to the rules file (default: rules.sif)")
    
    args = parser.parse_args()
    
    try:
        rules = parse_rules_file(args.rules_file)
        result = validate_thought(args.agent, args.content, rules)
        print(json.dumps(result, indent=2))
        
        if result.get("verdict") == "reject":
            sys.exit(1)

    except FileNotFoundError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()