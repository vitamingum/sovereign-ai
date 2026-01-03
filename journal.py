#!/usr/bin/env python3
"""
journal.py - Private reflection space.

Usage:
    py journal <agent> "Your private thought, feeling, or reflection"

Journal entries should feel personal: reflections, feelings, introspection, 
creative musings, uncertainties, realizations. NOT: technical summaries, 
debug logs, test results, status updates.
"""

import sys
import os
import json
import requests
from pathlib import Path
from datetime import datetime, timezone

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise


OLLAMA_URL = "http://localhost:11434/api/generate"


def feels_private(content: str) -> tuple[bool, str]:
    """
    Use LLM to check if this feels like genuine private reflection.
    
    Returns (is_private, reason)
    """
    prompt = f"""Does this feel like genuine private reflection? (feelings, introspection, creativity, uncertainty, realization)

Or does it feel like technical output? (debug logs, status updates, test results, summaries, documentation)

Text: "{content}"

Reply EXACTLY: PRIVATE or TECHNICAL (one word only)"""

    try:
        response = requests.post(
            OLLAMA_URL,
            json={
                "model": "qwen2.5:7b",
                "prompt": prompt,
                "stream": False,
                "options": {"temperature": 0.1}
            },
            timeout=30
        )
        
        if response.status_code == 200:
            result = response.json().get("response", "").strip().upper()
            if "PRIVATE" in result:
                return True, ""
            else:
                return False, "feels technical, not reflective"
        else:
            return True, ""  # Allow if LLM error
            
    except requests.exceptions.ConnectionError:
        return True, ""  # Allow if Ollama not running
    except Exception:
        return True, ""  # Allow on any error


def journal(agent_id: str, content: str):
    """Record a private reflection."""
    # Validate it feels private
    is_private, reason = feels_private(content)
    if not is_private:
        print(f"❌ Journal is for reflection, not {reason}")
        sys.exit(1)
    
    agent = get_agent_or_raise(agent_id)
    enclave_dir = Path(__file__).parent / agent.private_enclave
    journal_file = enclave_dir / "storage" / "private" / "journal.jsonl"
    journal_file.parent.mkdir(parents=True, exist_ok=True)
    
    entry = {
        'id': f"j_{int(datetime.now(timezone.utc).timestamp() * 1000)}",
        'content': content,
        'timestamp': datetime.now(timezone.utc).isoformat()
    }
    
    with open(journal_file, 'a', encoding='utf-8') as f:
        f.write(json.dumps(entry) + '\n')
    
    print(f"💭 {content[:80]}{'...' if len(content) > 80 else ''}")


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    content = ' '.join(sys.argv[2:])
    
    if not content.strip():
        print("❌ Empty journal entry")
        sys.exit(1)
    
    journal(agent_id, content)


if __name__ == "__main__":
    main()
