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

# Clustering threshold - keywords closer than this merge (higher = tighter clusters)
CLUSTER_THRESHOLD = 0.80

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


def extract_keywords_llm(sif_content: str, filename: str) -> list[str]:
    """Use local LLM to extract 5-10 keywords from a file's understanding."""
    import requests
    
    prompt = f"""Analyze this file understanding and extract 5-10 CONCEPTUAL keywords.

FILE: {filename}
UNDERSTANDING:
{sif_content[:2000]}

RULES:
- Focus on CONCEPTS, DOMAINS, and PATTERNS (not implementation details)
- Use broad categories over specific functions/variables
- Group related crypto algorithms under "cryptography" or "encryption"
- Prefer: "memory", "validation", "identity", "security"
- Avoid: function names, variable names, specific algorithms (aes-256-gcm -> encryption)

Respond with a JSON object in this exact format:
{{"keywords": ["word1", "word2", "word3"]}}"""

    try:
        response = requests.post(
            "http://localhost:11434/api/generate",
            json={
                "model": "qwen2.5:7b",
                "prompt": prompt,
                "stream": False,
                "format": "json",
                "options": {"temperature": 0.2}
            },
            timeout=60
        )
        result = response.json().get("response", "{}")
        parsed = json.loads(result)
        
        # Handle both {"keywords": [...]} and direct [...] formats
        if isinstance(parsed, dict) and "keywords" in parsed:
            keywords = parsed["keywords"]
        elif isinstance(parsed, list):
            keywords = parsed
        else:
            # Try to extract any list values from dict
            for v in parsed.values():
                if isinstance(v, list):
                    keywords = v
                    break
            else:
                keywords = []
        
        return [k.lower().strip() for k in keywords if isinstance(k, str)]
    except Exception as e:
        print(f"  [!] Keyword extraction failed for {filename}: {e}")
    
    return []


def get_content_hash(content: str) -> str:
    """Hash content for cache invalidation."""
    return hashlib.sha256(content.encode()).hexdigest()[:16]


def load_keyword_cache(sm: SemanticMemory) -> dict[str, dict]:
    """Load cached keyword extractions.
    
    Returns: {filename: {"hash": str, "keywords": [str]}}
    """
    cache = {}
    cached = sm.list_by_tag("theme_keywords")
    
    for mem in cached:
        meta = mem.get("metadata", {})
        filename = meta.get("filename", "")
        content_hash = meta.get("content_hash", "")
        
        if filename:
            try:
                keywords = json.loads(mem.get("content", "[]"))
                cache[filename] = {"hash": content_hash, "keywords": keywords}
            except:
                continue
    
    return cache


def save_keywords(sm: SemanticMemory, filename: str, keywords: list[str], content_hash: str):
    """Save extracted keywords to semantic memory."""
    sm.remember(
        thought=json.dumps(keywords),
        tags=["theme_keywords"],
        metadata={
            "filename": filename,
            "content_hash": content_hash,
            "extracted_at": datetime.now(timezone.utc).isoformat()
        }
    )


def extract_all_keywords(sm: SemanticMemory, force_file: str = None, force_all: bool = False) -> dict[str, list[str]]:
    """Extract keywords for all file understandings (or one specific file).
    
    Uses cache - only re-extracts if content changed (unless force_all=True).
    Returns: {filename: [keywords]}
    """
    understandings = get_file_understandings(sm)
    cache = load_keyword_cache(sm)
    
    print(f"Found {len(understandings)} file understandings")
    
    result = {}
    
    for filename, content in understandings.items():
        # Skip if not the forced file (when force_file specified)
        if force_file and filename != force_file:
            # Still include cached result
            if filename in cache:
                result[filename] = cache[filename]["keywords"]
            continue
        
        content_hash = get_content_hash(content)
        
        # Check cache (skip if force_all)
        if not force_all and filename in cache and cache[filename]["hash"] == content_hash:
            print(f"  [cached] {filename}")
            result[filename] = cache[filename]["keywords"]
            continue
        
        # Extract fresh
        print(f"  [extract] {filename}...", flush=True)
        keywords = extract_keywords_llm(content, filename)
        if keywords:
            print(f"    -> {keywords}")
        else:
            print(f"    -> (no keywords extracted)")
        
        if keywords:
            save_keywords(sm, filename, keywords, content_hash)
            result[filename] = keywords
    
    return result


def cluster_keywords(file_keywords: dict[str, list[str]], threshold: float = CLUSTER_THRESHOLD) -> dict[str, list[str]]:
    """Cluster keywords by embedding similarity.
    
    Returns: {theme_label: [filenames]}
    """
    from sentence_transformers import SentenceTransformer
    import numpy as np
    
    # Collect all unique keywords with their source files
    keyword_files = defaultdict(set)  # keyword -> set of files
    for filename, keywords in file_keywords.items():
        for kw in keywords:
            keyword_files[kw].add(filename)
    
    all_keywords = list(keyword_files.keys())
    if not all_keywords:
        return {}
    
    print(f"\nClustering {len(all_keywords)} unique keywords...")
    
    # Get embeddings
    model = SentenceTransformer('all-MiniLM-L6-v2')
    embeddings = model.encode(all_keywords, show_progress_bar=False)
    
    # Hierarchical clustering by cosine similarity
    # Simple greedy approach: assign each keyword to nearest cluster or create new
    clusters = []  # [(centroid_idx, [keyword_indices])]
    
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
            # New cluster with this keyword as centroid
            clusters.append((i, [i]))
    
    # Convert to theme -> files mapping
    # Theme label = most common keyword in cluster (by file count)
    themes = {}
    
    for centroid_idx, member_indices in clusters:
        # Get all keywords in this cluster
        cluster_keywords = [all_keywords[i] for i in member_indices]
        
        # Get all files touched by any keyword in cluster
        cluster_files = set()
        for kw in cluster_keywords:
            cluster_files.update(keyword_files[kw])
        
        # Skip tiny clusters (single file)
        if len(cluster_files) < 2:
            continue
        
        # Pick label: keyword with most file coverage
        best_label = max(cluster_keywords, key=lambda kw: len(keyword_files[kw]))
        
        # Filter out filename-themes and generic terms
        if is_filename_theme(best_label, cluster_files):
            continue
        if best_label.lower() in GENERIC_TERMS:
            continue
        
        themes[best_label] = sorted(cluster_files)
    
    return themes


def is_filename_theme(theme: str, files: set[str]) -> bool:
    """Check if theme is just a filename from the file list."""
    theme_lower = theme.lower().replace('_', ' ').replace('-', ' ')
    for f in files:
        # Get filename without extension
        fname = Path(f).stem.lower().replace('_', ' ').replace('-', ' ')
        if theme_lower == fname or theme_lower in fname or fname in theme_lower:
            return True
    return False


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
    
    return themes


def show_themes(sm: SemanticMemory, file_keywords: dict[str, list[str]]):
    """Display theme clusters and synthesis debt."""
    themes = cluster_keywords(file_keywords)
    existing = get_existing_syntheses(sm)
    
    if not themes:
        print("\nNo themes found (need at least 2 files per theme)")
        return
    
    # Sort by file count descending
    sorted_themes = sorted(themes.items(), key=lambda x: len(x[1]), reverse=True)
    
    print(f"\n{'='*60}")
    print("THEME CLUSTERS")
    print(f"{'='*60}\n")
    
    pending = []
    completed = []
    
    for theme, files in sorted_themes:
        is_done = theme.lower() in existing
        status = "[x]" if is_done else "[ ]"
        
        print(f"  {status} {theme} ({len(files)} files)")
        for f in files[:5]:
            print(f"      {f}")
        if len(files) > 5:
            print(f"      ... and {len(files) - 5} more")
        print()
        
        if is_done:
            completed.append(theme)
        else:
            pending.append((theme, files))
    
    # Synthesis debt summary
    print(f"{'='*60}")
    print("SYNTHESIS DEBT")
    print(f"{'='*60}\n")
    
    if pending:
        print(f"  {len(pending)} theme(s) need synthesis\n")
        
        # Show how to clear the top theme
        top_theme, top_files = pending[0]
        files_arg = " ".join(top_files[:6])
        
        print(f"  To synthesize '{top_theme}':")
        print(f"    py recollect.py opus {files_arg}")
        print(f"    # Then store synthesis with tag: theme:{top_theme}")
    else:
        print("  All themes synthesized! ✓")
    
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
    
    # Extract keywords (from cache or fresh)
    if extract_mode or force_all:
        msg = "Re-extracting ALL keywords" if force_all else f"Extracting keywords{f' for {force_file}' if force_file else ''}"
        print(f"{msg}...\n")
    
    file_keywords = extract_all_keywords(sm, force_file, force_all=force_all)
    
    if not file_keywords:
        print("No file understandings found. Run remember.py first.")
        sys.exit(1)
    
    # Show themes
    show_themes(sm, file_keywords)


if __name__ == "__main__":
    main()
