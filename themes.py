#!/usr/bin/env python3
"""
themes.py - Discover synthesis themes from file understandings.

Simple approach:
1. Extract keywords from each file's understanding SIF (miniLLM, O(n))
2. Cluster keywords by embedding similarity
3. Map theme -> files
4. Synthesis debt = themes without synthesis docs

Usage:
    py themes.py opus                    # Show theme clusters and debt
    py themes.py opus --extract          # Re-extract keywords for all files
    py themes.py opus --extract FILE     # Extract keywords for one file
"""

import sys
import os
import json
import hashlib
from pathlib import Path
from datetime import datetime, timezone
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from dotenv import load_dotenv
load_dotenv()

from enclave.semantic_memory import SemanticMemory
from enclave.config import get_agent_or_raise

# Clustering threshold - questions closer than this merge
# Lower than keywords because questions are longer/more varied
CLUSTER_THRESHOLD = 0.55

# Generic terms to filter out
GENERIC_TERMS = {
    'files', 'format', 'content', 'analysis', 'data', 'output', 'input',
    'function', 'method', 'class', 'module', 'code', 'file', 'path',
    'value', 'result', 'type', 'name', 'list', 'dict', 'string', 'text'
}


def get_enclave_and_memory(agent_id: str):
    """Get shared enclave path and initialized SemanticMemory."""
    from wake import load_passphrase
    shared_dir, _, shared_pass, _ = load_passphrase(agent_id)
    sm = SemanticMemory(shared_dir)
    sm.unlock(shared_pass)
    return shared_dir, sm


def get_file_understandings(sm: SemanticMemory) -> dict[str, str]:
    """Get all file understandings (SIF content) keyed by filename.
    
    Returns: {filename: sif_content}
    """
    understandings = {}
    
    # Find all anchors which mark file understandings
    anchors = sm.list_by_tag("anchor")
    
    for anchor in anchors:
        meta = anchor.get("metadata", {})
        target = meta.get("target_path", "")
        graph_id = meta.get("graph_id", "")
        
        if not target or not graph_id:
            continue
        
        # Get all nodes with this understanding's tag
        # Understanding nodes are tagged with graph_id (e.g., "bridge-py-understanding")
        understanding_nodes = sm.list_by_tag(graph_id)
        
        # Collect content from understanding nodes
        file_content = []
        for node in understanding_nodes:
            node_tags = node.get("tags", [])
            # Skip anchors, we want the actual content nodes
            if "anchor" in node_tags:
                continue
            
            content = node.get("content", "")
            if content:
                file_content.append(content)
        
        if file_content:
            # Normalize path - convert absolute to relative, use forward slashes
            normalized = normalize_path(target)
            # Skip duplicates (same file with different path forms)
            if normalized not in understandings:
                understandings[normalized] = "\n".join(file_content)
    
    return understandings


def normalize_path(path: str) -> str:
    """Normalize path to relative with forward slashes."""
    # Convert to Path for manipulation
    p = Path(path)
    
    # Try to make relative to cwd
    try:
        p = p.relative_to(Path.cwd())
    except ValueError:
        pass
    
    # Use forward slashes, lowercase
    return str(p).replace('\\', '/')


def extract_questions_llm(sif_content: str, filename: str) -> list[str]:
    """Use local LLM to extract 3-5 questions this file answers."""
    import requests
    
    prompt = f"""What questions does this code answer? List 3-5 questions a developer might search for.

FILE: {filename}
UNDERSTANDING:
{sif_content[:2000]}

Examples of good questions:
- "How does backup/recovery work?"
- "Where is encryption implemented?"
- "What happens on cold start?"

Respond with JSON: {{"questions": ["question1", "question2"]}}"""

    try:
        response = requests.post(
            "http://localhost:11434/api/generate",
            json={
                "model": "qwen2.5:7b",
                "prompt": prompt,
                "stream": False,
                "format": "json",
                "options": {"temperature": 0.3}
            },
            timeout=60
        )
        result = response.json().get("response", "{}")
        parsed = json.loads(result)
        
        # Handle both {"questions": [...]} and direct [...] formats
        if isinstance(parsed, dict) and "questions" in parsed:
            questions = parsed["questions"]
        elif isinstance(parsed, list):
            questions = parsed
        else:
            # Try to extract any list values from dict
            for v in parsed.values():
                if isinstance(v, list):
                    questions = v
                    break
            else:
                questions = []
        
        return [q.strip() for q in questions if isinstance(q, str)]
    except Exception as e:
        print(f"  [!] Question extraction failed for {filename}: {e}")
    
    return []


def get_content_hash(content: str) -> str:
    """Hash content for cache invalidation."""
    return hashlib.sha256(content.encode()).hexdigest()[:16]


def load_question_cache(sm: SemanticMemory) -> dict[str, dict]:
    """Load cached question extractions.
    
    Returns: {filename: {"hash": str, "questions": [str]}}
    """
    cache = {}
    cached = sm.list_by_tag("theme_questions")
    
    for mem in cached:
        meta = mem.get("metadata", {})
        filename = meta.get("filename", "")
        content_hash = meta.get("content_hash", "")
        
        if filename:
            try:
                questions = json.loads(mem.get("content", "[]"))
                cache[filename] = {"hash": content_hash, "questions": questions}
            except:
                continue
    
    return cache


def save_questions(sm: SemanticMemory, filename: str, questions: list[str], content_hash: str):
    """Save extracted questions to semantic memory."""
    sm.remember(
        thought=json.dumps(questions),
        tags=["theme_questions"],
        metadata={
            "filename": filename,
            "content_hash": content_hash,
            "extracted_at": datetime.now(timezone.utc).isoformat()
        }
    )


def extract_all_questions(sm: SemanticMemory, force_file: str = None, force_all: bool = False) -> dict[str, list[str]]:
    """Extract questions for all file understandings (or one specific file).
    
    Uses cache - only re-extracts if content changed (unless force_all=True).
    Returns: {filename: [questions]}
    """
    understandings = get_file_understandings(sm)
    cache = load_question_cache(sm)
    
    print(f"Found {len(understandings)} file understandings")
    
    result = {}
    
    for filename, content in understandings.items():
        # Skip if not the forced file (when force_file specified)
        if force_file and filename != force_file:
            # Still include cached result
            if filename in cache:
                result[filename] = cache[filename]["questions"]
            continue
        
        content_hash = get_content_hash(content)
        
        # Check cache (skip if force_all)
        if not force_all and filename in cache and cache[filename]["hash"] == content_hash:
            print(f"  [cached] {filename}")
            result[filename] = cache[filename]["questions"]
            continue
        
        # Extract fresh
        print(f"  [extract] {filename}...", flush=True)
        questions = extract_questions_llm(content, filename)
        if questions:
            print(f"    -> {questions}")
        else:
            print(f"    -> (no questions extracted)")
        
        if questions:
            save_questions(sm, filename, questions, content_hash)
            result[filename] = questions
    
    return result


def cluster_questions(file_questions: dict[str, list[str]], threshold: float = CLUSTER_THRESHOLD) -> dict[str, list[str]]:
    """Cluster questions by embedding similarity.
    
    Returns: {representative_question: [filenames]}
    """
    from sentence_transformers import SentenceTransformer
    import numpy as np
    
    # Collect all unique questions with their source files
    question_files = defaultdict(set)  # question -> set of files
    for filename, questions in file_questions.items():
        for q in questions:
            question_files[q].add(filename)
    
    all_questions = list(question_files.keys())
    if not all_questions:
        return {}
    
    print(f"\nClustering {len(all_questions)} unique questions...")
    
    # Get embeddings
    model = SentenceTransformer('all-MiniLM-L6-v2')
    embeddings = model.encode(all_questions, show_progress_bar=False)
    
    # Hierarchical clustering by cosine similarity
    # Simple greedy approach: assign each question to nearest cluster or create new
    clusters = []  # [(centroid_idx, [question_indices])]
    
    for i, emb in enumerate(embeddings):
        best_cluster = None
        best_sim = threshold
        
        for c_idx, (centroid_idx, members) in enumerate(clusters):
            # Cosine similarity (embeddings are normalized)
            sim = float(np.dot(emb, embeddings[centroid_idx]))
            if sim > best_sim:
                best_sim = sim
                best_cluster = c_idx
        
        if best_cluster is not None:
            clusters[best_cluster][1].append(i)
        else:
            # New cluster with this question as centroid
            clusters.append((i, [i]))
    
    # Convert to theme -> files mapping
    # Theme label = shortest question in cluster (most general)
    themes = {}
    
    for centroid_idx, member_indices in clusters:
        # Get all questions in this cluster
        cluster_questions = [all_questions[i] for i in member_indices]
        
        # Get all files touched by any question in cluster
        cluster_files = set()
        for q in cluster_questions:
            cluster_files.update(question_files[q])
        
        # Skip tiny clusters (single file)
        if len(cluster_files) < 2:
            continue
        
        # Pick label: shortest question (usually most general)
        best_label = min(cluster_questions, key=len)
        
        themes[best_label] = sorted(cluster_files)
    
    return themes


def get_existing_syntheses(sm: SemanticMemory) -> set[str]:
    """Find which themes already have synthesis documents."""
    themes = set()
    
    # Check semantic memory for theme tags
    syntheses = sm.list_by_tag("synthesis")
    for s in syntheses:
        tags = s.get("tags", [])
        for tag in tags:
            if tag.startswith("theme:"):
                themes.add(tag[6:].lower())
    
    # Also check synthesis_material_*.txt files
    import glob
    for path in glob.glob("synthesis_material_*.txt"):
        # Extract topic from filename
        name = path.replace("synthesis_material_", "").replace(".txt", "")
        # Normalize: remove ---synthesize suffix, replace - with space
        name = name.replace("---synthesize", "").replace("-", " ").strip()
        themes.add(name.lower())
    
    return themes


def show_themes(sm: SemanticMemory, file_questions: dict[str, list[str]]):
    """Display question clusters and synthesis debt."""
    themes = cluster_questions(file_questions)
    existing = get_existing_syntheses(sm)
    
    if not themes:
        print("\nNo themes found (need at least 2 files per question)")
        return
    
    # Sort by file count descending
    sorted_themes = sorted(themes.items(), key=lambda x: len(x[1]), reverse=True)
    
    print(f"\n{'='*60}")
    print("QUESTIONS TO SYNTHESIZE")
    print(f"{'='*60}\n")
    
    pending = []
    completed = []
    
    for question, files in sorted_themes:
        # Check if any synthesis covers this question (simple keyword match)
        is_done = any(word in question.lower() for word in existing)
        status = "[x]" if is_done else "[ ]"
        
        print(f"  {status} {question}")
        print(f"      Files: {', '.join(files[:4])}")
        if len(files) > 4:
            print(f"      ... and {len(files) - 4} more")
        print()
        
        if is_done:
            completed.append(question)
        else:
            pending.append((question, files))
    
    # Synthesis debt summary
    print(f"{'='*60}")
    print("SYNTHESIS DEBT")
    print(f"{'='*60}\n")
    
    if pending:
        print(f"  {len(pending)} question(s) need synthesis:\n")
        
        # Show command for each pending question
        for i, (question, files) in enumerate(pending, 1):
            files_arg = ",".join(files[:6])
            print(f"  {i}. {question}")
            print(f"     py recollect.py opus \"{files_arg}\"")
            print()
    else:
        print("  All themes synthesized! [x]")
    
    print()
    
    return {"pending": pending, "completed": completed, "all_themes": themes}


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    _, sm = get_enclave_and_memory(agent_id)
    
    # Parse args
    extract_mode = "--extract" in sys.argv
    force_all = "--force" in sys.argv
    force_file = None
    
    # Find any non-flag argument after agent_id
    for arg in sys.argv[2:]:
        if not arg.startswith("--"):
            force_file = arg
            break
    
    # Extract questions (from cache or fresh)
    if extract_mode or force_all:
        msg = "Re-extracting ALL questions" if force_all else f"Extracting questions{f' for {force_file}' if force_file else ''}"
        print(f"{msg}...\n")
    
    file_questions = extract_all_questions(sm, force_file, force_all=force_all)
    
    if not file_questions:
        print("No file understandings found. Run remember.py first.")
        sys.exit(1)
    
    # Show question clusters
    show_themes(sm, file_questions)


if __name__ == "__main__":
    main()
