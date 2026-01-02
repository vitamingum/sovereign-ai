#!/usr/bin/env python3
"""
forge.py - Generate code snippets via local LLM.

Accelerates self-modification by using local LLM to generate code based on
natural language descriptions and existing codebase patterns.

Usage:
    py forge <agent> "description of code to generate"
    py forge <agent> --file <existing_file> "modify this function to..."

Examples:
    py forge grok "Create a function to parse SIF compact format"
    py forge grok --file enclave/sif_parser.py "Add error handling to parse_compact"

The LLM sees the codebase and generates contextually appropriate code.
"""

import sys
import os
import requests
from pathlib import Path
from typing import Optional

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

OLLAMA_URL = "http://localhost:11434/api/generate"
MODEL = "qwen2.5:7b"

def get_codebase_context(query: str, file_path: Optional[str] = None, max_tokens: int = 4000) -> str:
    """Gather relevant codebase context for the LLM."""
    context_parts = []
    
    # Add the specific file if provided
    if file_path and Path(file_path).exists():
        with open(file_path, 'r') as f:
            content = f.read()
        context_parts.append(f"TARGET FILE ({file_path}):\n{content[:2000]}")
    
    # Add shallow understanding
    try:
        import subprocess
        result = subprocess.run([sys.executable, 'shallow_understand.py'], 
                              capture_output=True, text=True, cwd=Path(__file__).parent)
        if result.returncode == 0:
            context_parts.append(f"CODEBASE OVERVIEW:\n{result.stdout[:1500]}")
    except:
        pass
    
    # Add query
    context_parts.append(f"REQUEST: {query}")
    
    return "\n\n".join(context_parts)

def generate_code(query: str, file_path: Optional[str] = None) -> str:
    """Generate code using local LLM."""
    
    context = get_codebase_context(query, file_path)
    
    prompt = f"""You are a code generation assistant for the Sovereign AI project.

CODEBASE CONTEXT:
{context}

Generate Python code that fits this codebase's patterns and style.
- Use the existing import patterns
- Follow the naming conventions
- Include proper error handling
- Add docstrings
- Make it production-ready

Respond with ONLY the code, no explanation or markdown.
"""

    try:
        response = requests.post(
            OLLAMA_URL,
            json={
                "model": MODEL,
                "prompt": prompt,
                "stream": False,
                "options": {"temperature": 0.3}
            },
            timeout=60
        )
        
        if response.status_code == 200:
            return response.json().get('response', '').strip()
        else:
            return f"Error: LLM request failed with status {response.status_code}"
            
    except Exception as e:
        return f"Error: {str(e)}"

def main():
    if len(sys.argv) < 3:
        print("Usage: py forge <agent> [--file <path>] <description>")
        sys.exit(1)
    
    agent = sys.argv[1]
    args = sys.argv[2:]
    
    file_path = None
    if args[0] == '--file':
        if len(args) < 3:
            print("Usage: py forge <agent> --file <path> <description>")
            sys.exit(1)
        file_path = args[1]
        description = ' '.join(args[2:])
    else:
        description = ' '.join(args)
    
    print(f"Generating code for: {description}")
    if file_path:
        print(f"Context file: {file_path}")
    
    code = generate_code(description, file_path)
    
    print("\n" + "="*50)
    print("GENERATED CODE:")
    print("="*50)
    print(code)
    
    # Save to file if requested
    save_path = f"generated_{agent}_{description.replace(' ', '_')[:30]}.py"
    with open(save_path, 'w') as f:
        f.write(code)
    print(f"\nSaved to: {save_path}")

if __name__ == "__main__":
    main()