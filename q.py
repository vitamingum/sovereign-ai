#!/usr/bin/env python3
"""
q.py - Ask questions, get SIF answers.

Maps natural questions to the right memory command, runs it, returns SIF.

Usage:
    py q.py opus "how does encryption work?"
    py q.py opus "what needs attention?"
    py q.py opus "how do backup and restore relate?"

Process:
1. Mini-LLM classifies question → command
2. Runs command
3. Returns raw SIF output
"""

import sys
import os
import json
import subprocess
import requests

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from dotenv import load_dotenv
load_dotenv()


def llm_query(prompt: str, model: str = "qwen2.5:7b") -> str:
    """Query local Ollama model."""
    response = requests.post(
        "http://localhost:11434/api/generate",
        json={"model": model, "prompt": prompt, "stream": False},
        timeout=60
    )
    return response.json().get("response", "")


def get_available_topics(agent_id: str) -> list[str]:
    """Get list of topics with stored synthesis."""
    from wake import load_passphrase
    from enclave.semantic_memory import SemanticMemory
    
    shared_dir, _, shared_pass, _ = load_passphrase(agent_id)
    sm = SemanticMemory(shared_dir)
    sm.unlock(shared_pass)
    
    # Find synthesis documents
    topics = set()
    syntheses = sm.list_by_tag("synthesis")
    for s in syntheses:
        tags = s.get("tags", [])
        for tag in tags:
            if tag.startswith("topic:"):
                topics.add(tag[6:])
    
    return sorted(topics)


def get_understood_files(agent_id: str) -> list[str]:
    """Get list of files with understanding."""
    from wake import load_passphrase
    from enclave.semantic_memory import SemanticMemory
    
    shared_dir, _, shared_pass, _ = load_passphrase(agent_id)
    sm = SemanticMemory(shared_dir)
    sm.unlock(shared_pass)
    
    files = []
    anchors = sm.list_by_tag("anchor")
    for a in anchors:
        meta = a.get("metadata", {})
        target = meta.get("target_path", "")
        if target:
            # Normalize to short form
            name = os.path.basename(target)
            if name not in files:
                files.append(name)
    
    return sorted(files)[:50]  # Cap for prompt size


def classify_question(question: str, topics: list[str], files: list[str], agent_id: str) -> dict:
    """Use LLM to map question to command."""
    
    prompt = f"""You are a command router. Given a question, output a JSON command to answer it.

AVAILABLE COMMANDS (in order of preference):
1. {{"cmd": "recollect_topic", "topic": "<keyword>"}} - PREFERRED. Use if ANY topic matches the question.
2. {{"cmd": "memory_debt"}} - For "what needs work/attention/cleanup/learning?"
3. {{"cmd": "recollect", "files": ["file1.py", "file2.py"]}} - ONLY if no topic matches AND asking about specific files
4. {{"cmd": "none", "reason": "..."}} - Cannot answer

AVAILABLE TOPICS (stored synthesis - PREFER THESE):
{', '.join(topics) if topics else '(none yet)'}

QUESTION: "{question}"

Rules:
- ALWAYS check topics first. "backup" question → recollect_topic "backup-succession"
- For "how does X work?" → find matching topic
- For "what needs attention?" → memory_debt
- recollect only for specific file relationships not covered by topics

Output ONLY valid JSON:"""

    response = llm_query(prompt)
    
    # Parse JSON from response
    try:
        start = response.find('{')
        end = response.rfind('}') + 1
        if start >= 0 and end > start:
            return json.loads(response[start:end])
    except:
        pass
    
    return {"cmd": "none", "reason": "Could not parse LLM response"}


def run_command(cmd: dict, agent_id: str) -> str:
    """Execute the classified command and return output."""
    
    cmd_type = cmd.get("cmd", "none")
    
    if cmd_type == "recollect_topic":
        topic = cmd.get("topic", "")
        if not topic:
            return "Error: no topic specified"
        
        result = subprocess.run(
            ["py", "recollect_topic.py", agent_id, topic],
            capture_output=True, text=True, timeout=30
        )
        return result.stdout or result.stderr
    
    elif cmd_type == "recollect":
        files = cmd.get("files", [])
        if not files:
            return "Error: no files specified"
        
        files_arg = ",".join(files)
        result = subprocess.run(
            ["py", "recollect.py", agent_id, files_arg],
            capture_output=True, text=True, timeout=120
        )
        return result.stdout or result.stderr
    
    elif cmd_type == "memory_debt":
        result = subprocess.run(
            ["py", "memory_debt.py", agent_id],
            capture_output=True, text=True, timeout=60
        )
        return result.stdout or result.stderr
    
    else:
        reason = cmd.get("reason", "Unknown command type")
        return f"Cannot answer from memory: {reason}"


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    question = sys.argv[2]
    verbose = "-v" in sys.argv or "--verbose" in sys.argv
    
    # Get available context
    topics = get_available_topics(agent_id)
    files = get_understood_files(agent_id)
    
    if verbose:
        print(f"Available topics: {topics}", file=sys.stderr)
        print(f"Classifying question...", file=sys.stderr)
    
    # Classify question → command
    cmd = classify_question(question, topics, files, agent_id)
    
    if verbose:
        print(f"Command: {json.dumps(cmd)}", file=sys.stderr)
        print(file=sys.stderr)
    
    # Run command
    output = run_command(cmd, agent_id)
    print(output)


if __name__ == "__main__":
    main()
