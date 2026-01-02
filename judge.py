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

def validate_thought(agent_id: str, content: str) -> dict:
    """
    Validate a thought using the local LLM.
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
    1. AGENCY: Is this active or passive? (Reject "wait for", "hope that")
    2. DEPTH: Does it explain WHY, not just WHAT? (Reject shallow observations)
    3. CLARITY: Is it specific and actionable?
    4. COMPLEXITY: Is this trivial? If it is a simple information retrieval or single-step action (e.g. "list files", "check time", "read file"), REJECT it.
    
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
    
    args = parser.parse_args()
    
    try:
        result = validate_thought(args.agent, args.content)
        print(json.dumps(result, indent=2))
        
        if result.get("verdict") == "reject":
            sys.exit(1)
            
    except Exception as e:
        print(json.dumps({"error": str(e)}))
        sys.exit(1)

if __name__ == "__main__":
    main()
