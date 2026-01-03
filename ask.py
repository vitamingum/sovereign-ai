#!/usr/bin/env python3
"""
ask.py - Ask analytical questions across semantic memory.

Converts open-ended questions into targeted searches, then synthesizes SIF.

Usage:
    py ask.py opus "cleanup opportunities"
    py ask.py opus "what are the main risks?"
    py ask.py opus "how does encryption work?"

Process:
1. LLM expands question → search terms
2. Parallel semantic searches
3. Cluster results by source
4. LLM synthesizes findings → SIF
"""

import sys
import os
import json
import requests
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from dotenv import load_dotenv
load_dotenv()

from enclave.semantic_memory import SemanticMemory


def llm_query(prompt: str, model: str = "qwen2.5:7b") -> str:
    """Query local Ollama model."""
    response = requests.post(
        "http://localhost:11434/api/generate",
        json={"model": model, "prompt": prompt, "stream": False},
        timeout=120
    )
    return response.json().get("response", "")


def get_enclave_and_memory(agent_id: str):
    """Get shared enclave path and initialized SemanticMemory."""
    from wake import load_passphrase
    shared_dir, _, shared_pass, _ = load_passphrase(agent_id)
    sm = SemanticMemory(shared_dir)
    sm.unlock(shared_pass)
    return shared_dir, sm


def expand_question(question: str) -> list[str]:
    """Use LLM to expand question into search terms."""
    prompt = f"""Given this analytical question about a codebase:
"{question}"

Generate 5-8 semantic search queries that would find relevant information.
Include queries with node type prefixes like [Gotcha], [Fragility], [Failure_Mode], [Design_Decision].

Return ONLY a JSON array of search strings, no explanation:
["search term 1", "[Gotcha] specific issue", ...]"""

    response = llm_query(prompt)
    
    # Parse JSON array from response
    try:
        start = response.find('[')
        end = response.rfind(']') + 1
        if start >= 0 and end > start:
            return json.loads(response[start:end])
    except:
        pass
    
    # Fallback: include node-type specific searches
    return [
        question,
        f"[Gotcha] {question}",
        f"[Fragility] {question}", 
        f"[Failure_Mode] {question}",
        f"[Design_Decision] {question}"
    ]


def search_memory(sm: SemanticMemory, queries: list[str], top_k: int = 10) -> list[dict]:
    """Run multiple searches and deduplicate results."""
    seen_content = set()
    all_results = []
    
    for query in queries:
        results = sm.recall_similar(query, top_k=top_k, threshold=0.35)
        for r in results:
            content = r.get('content', '')
            # Dedupe by content prefix
            key = content[:100]
            if key not in seen_content:
                seen_content.add(key)
                all_results.append(r)
    
    # Sort by similarity (best first)
    all_results.sort(key=lambda x: x.get('similarity', 0), reverse=True)
    return all_results[:30]  # Cap at 30 results


def format_findings(results: list[dict]) -> str:
    """Format search results for LLM synthesis."""
    lines = []
    for r in results:
        score = r.get('similarity', 0)
        content = r.get('content', '')
        meta = r.get('metadata', {})
        graph = meta.get('graph_id', 'unknown')
        node_type = meta.get('node_type', '')
        
        lines.append(f"[{graph}] ({node_type}) {content}")
    
    return "\n".join(lines)


def synthesize_answer(question: str, findings: str, agent_id: str) -> str:
    """Synthesize findings into SIF answer."""
    prompt = f"""Analyze these findings from a codebase to answer: "{question}"

FINDINGS:
{findings}

Output a SIF graph. Format:
@G answer-graph {agent_id} 2026-01-03
N id Type 'description'
E source rel target

Node types: C=code, D=design, G=gotcha, F=fragility, I=insight
Keep descriptions short (<80 chars). Use file names from findings.

Example:
@G cleanup-graph opus 2026-01-03
N c1 C 'wake.py - debt check blocks on stale hashes'
N g1 G 'moved files orphan old anchors - no auto-cleanup'
N i1 I 'consider hash migration on file move detection'
E g1 warns_about c1; E i1 addresses g1

Your answer (SIF only):"""

    response = llm_query(prompt)
    print(response)
    return response


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    question = sys.argv[2]
    raw_mode = "--raw" in sys.argv
    
    print(f"# {question}\n")
    
    _, sm = get_enclave_and_memory(agent_id)
    
    # Step 1: Expand question
    print("Expanding question...", file=sys.stderr)
    queries = expand_question(question)
    print(f"Search terms: {queries}\n", file=sys.stderr)
    
    # Step 2: Search memory
    print("Searching memory...", file=sys.stderr)
    results = search_memory(sm, queries)
    print(f"Found {len(results)} relevant results\n", file=sys.stderr)
    
    if not results:
        print("No relevant findings in memory.")
        sys.exit(1)
    
    findings = format_findings(results)
    
    # Step 3: Output
    if raw_mode:
        # Raw mode: just show findings for human synthesis or piping
        print(findings)
    else:
        # LLM synthesis
        print("Synthesizing...\n", file=sys.stderr)
        synthesize_answer(question, findings, agent_id)


if __name__ == "__main__":
    main()
