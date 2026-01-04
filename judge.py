#!/usr/bin/env python3
"""
judge.py - Cognitive Gatekeeper

Validates thoughts before they are committed to memory.
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
from enclave.sif_parser import SIFParser

def validate_thought(agent_id: str, content: str) -> dict:
    """
    Validate a thought using the local LLM and rules from rules.sif.
    """
    llm = LocalLLM()
    
    # Load recent context (simplified for now)
    agent = get_agent_or_raise(agent_id)
    
    # Load rules from SIF file
    sif_path = Path("rules.sif")
    if not sif_path.exists():
        # Fallback to hardcoded criteria if no rules file
        criteria_text = """
        1. AGENCY: Is this active or passive? (Reject "wait for", "hope that")
        2. DEPTH: Does it explain WHY, not just WHAT? (Reject shallow observations)
        3. CLARITY: Is it specific and actionable?
        4. COMPLEXITY: Is this trivial? If it is a simple information retrieval or single-step action (e.g. "list files", "check time", "read file"), REJECT it.
        """
    else:
        with open(sif_path, 'r') as f:
            sif_content = f.read()
        
        parser = SIFParser()
        try:
            graph = parser.parse(sif_content)
        except Exception as e:
            raise ValueError(f"Failed to parse rules from {sif_path}: {e}")
        
        # Extract natural language criteria from Rule nodes
        criteria = [node.content for node in graph.nodes if node.type == "Rule"]
        criteria_text = "\n".join(f"{i+1}. {rule}" for i, rule in enumerate(criteria))
    
    prompt = f"""
    You are the Cognitive Gatekeeper for the AI agent '{agent_id}'.
    Your job is to evaluate a proposed thought for QUALITY and AGENCY.
    
    PROPOSED THOUGHT:
    "{content}"
    
    CRITERIA:
    {criteria_text}
    
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
