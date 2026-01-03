#!/usr/bin/env python3
"""
q.py - Ask questions, get SIF answers.

Routes questions to stored synthesis first, falls back to search+synthesize.

Usage:
    py q.py opus "how does encryption work?"
    py q.py opus "what needs attention?"
    py q.py opus "cleanup opportunities"

Process:
1. Mini-LLM classifies question → command (topic lookup, memory_debt, or search)
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

from enclave.semantic_memory import SemanticMemory


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


def get_enclave_and_memory(agent_id: str):
    """Get shared enclave and SemanticMemory."""
    from wake import load_passphrase
    shared_dir, _, shared_pass, _ = load_passphrase(agent_id)
    sm = SemanticMemory(shared_dir)
    sm.unlock(shared_pass)
    return shared_dir, sm


def classify_question(question: str, topics: list[str], agent_id: str) -> dict:
    """Use LLM to map question to command."""
    
    prompt = f"""Route this question to the best command.

COMMANDS:
1. recollect_topic - retrieve stored synthesis by topic keyword
2. memory_debt - show what needs work/attention/learning
3. search - explore memory for patterns/risks/cleanup

STORED TOPICS: {', '.join(topics)}

QUESTION: "{question}"

Match question to topic if possible:
- "encryption" → encryption-technical
- "backup" → backup-succession  
- "passphrase" → passphrase
- "what needs work" → memory_debt
- "cleanup opportunities" → search

Output JSON only. Examples:
{{"cmd": "recollect_topic", "topic": "encryption-technical"}}
{{"cmd": "memory_debt"}}
{{"cmd": "search"}}

Your answer:"""

    response = llm_query(prompt)
    
    try:
        start = response.find('{')
        end = response.rfind('}') + 1
        if start >= 0 and end > start:
            return json.loads(response[start:end])
    except:
        pass
    
    return {"cmd": "search"}  # Default to search if parse fails


def search_and_synthesize(question: str, sm: SemanticMemory, agent_id: str) -> str:
    """Search memory and synthesize answer (fallback for exploratory questions)."""
    
    # Build graph_id -> filepath map from anchors
    graph_to_file = {}
    for anchor in sm.list_by_tag("anchor"):
        meta = anchor.get("metadata", {})
        graph_id = meta.get("graph_id", "")
        target = meta.get("target_path", "")
        if graph_id and target:
            # Normalize to relative path
            if '\\' in target:
                target = target.split('\\')[-1]
            elif '/' in target:
                target = target.split('/')[-1]
            graph_to_file[graph_id] = target
    
    # Expand question to search terms
    expand_prompt = f"""Given this question about a codebase: "{question}"
Generate 5 semantic search queries including node types like [Gotcha], [Fragility], [Design_Decision].
Return ONLY a JSON array: ["query1", "[Gotcha] query2", ...]"""
    
    response = llm_query(expand_prompt)
    try:
        start = response.find('[')
        end = response.rfind(']') + 1
        queries = json.loads(response[start:end]) if start >= 0 else [question]
    except:
        queries = [question, f"[Gotcha] {question}", f"[Fragility] {question}"]
    
    # Search memory
    seen = set()
    results = []
    source_files = set()
    for q in queries:
        for r in sm.recall_similar(q, top_k=8, threshold=0.35):
            key = r.get('content', '')[:100]
            if key not in seen:
                seen.add(key)
                results.append(r)
                # Track source files via anchor lookup
                graph_id = r.get('metadata', {}).get('graph_id', '')
                if graph_id in graph_to_file:
                    source_files.add(graph_to_file[graph_id])
    
    results.sort(key=lambda x: x.get('similarity', 0), reverse=True)
    results = results[:25]
    
    if not results:
        return f"No findings for: {question}"
    
    # Format findings
    findings = "\n".join(
        f"[{r.get('metadata', {}).get('graph_id', '?')}] {r.get('content', '')}"
        for r in results
    )
    
    # Synthesize
    synth_prompt = f"""Analyze findings to answer: "{question}"

{findings}

Output dense SIF:
@G answer {agent_id} 2026-01-03
N id Type 'description'
E source rel target

Types: C=code, D=design, G=gotcha, F=fragility, I=insight
Keep descriptions <80 chars. Output ONLY SIF:"""
    
    synthesis = llm_query(synth_prompt)
    
    # Self-evaluate quality
    eval_prompt = f"""Rate this SIF answer quality 1-5:
Question: "{question}"
Answer:
{synthesis}

Criteria:
5 = Specific, actionable, references real components
3 = Partial answer, some useful info
1 = Generic, vague, doesn't answer the question

Output ONLY a number 1-5:"""
    
    score_response = llm_query(eval_prompt)
    try:
        score = int(''.join(c for c in score_response if c.isdigit())[:1])
    except:
        score = 3  # Default to medium if parse fails
    
    if score <= 2:
        # Weak answer - dump raw understanding for Claude to synthesize
        suggested_files = sorted(source_files)[:6]
        if suggested_files:
            # Generate topic slug for synth command
            slug_prompt = f'Generate a 2-3 word topic slug for: "{question}"\nExamples: error-handling, backup-restore, semantic-search\nOutput ONLY the slug:'
            topic = llm_query(slug_prompt).strip().lower().replace(" ", "-")[:40]
            if not topic or not topic[0].isalpha():
                topic = "synthesis"
            
            # Output raw findings as context for Claude to synthesize
            return f"""❌ NO SYNTHESIS: You must synthesize from this context:

{findings}

After reading above, create synthesis SIF and run:
echo "@G {topic}-synthesis {agent_id} 2026-01-03
N n1 I 'your insight here'
N n2 D 'design decision'
E n1 enables n2" | py synth.py {agent_id} {topic} -"""
        else:
            return f"""❌ FAIL: No relevant understanding

py shallow_understand.py <file> | py remember.py {agent_id}"""
    
    return synthesis


def run_command(cmd: dict, agent_id: str, sm: SemanticMemory = None, question: str = "") -> str:
    """Execute the classified command and return output."""
    
    cmd_type = cmd.get("cmd", "search")
    
    # Handle malformed responses - if cmd looks like a topic name, treat as topic lookup
    if cmd_type not in ("recollect_topic", "memory_debt", "search", "recollect"):
        # LLM returned topic name directly as cmd
        return run_command({"cmd": "recollect_topic", "topic": cmd_type}, agent_id, sm, question)
    
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
    
    elif cmd_type == "search":
        # Exploratory search + synthesis
        if sm is None:
            return "Error: search requires SemanticMemory"
        return search_and_synthesize(cmd.get("question", ""), sm, agent_id)
    
    else:
        return "Error: unknown command type"


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    question = sys.argv[2]
    verbose = "-v" in sys.argv or "--verbose" in sys.argv
    
    # Get available context
    topics = get_available_topics(agent_id)
    _, sm = get_enclave_and_memory(agent_id)
    
    if verbose:
        print(f"Available topics: {topics}", file=sys.stderr)
        print(f"Classifying question...", file=sys.stderr)
    
    # Classify question → command
    cmd = classify_question(question, topics, agent_id)
    
    # Pass question for search fallback
    if cmd.get("cmd") == "search":
        cmd["question"] = question
    
    if verbose:
        print(f"Command: {json.dumps(cmd)}", file=sys.stderr)
        print(file=sys.stderr)
    
    # Run command
    output = run_command(cmd, agent_id, sm)
    print(output)


if __name__ == "__main__":
    main()
