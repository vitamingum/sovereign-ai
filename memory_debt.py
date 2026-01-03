#!/usr/bin/env python3
"""
memory_debt.py - Track all memory debt in one place.

Memory debt = knowledge not yet committed to semantic memory

Two types:
  1. Understanding debt: files changed since last remember.py
  2. Synthesis debt: cross-file questions without synthesis

Usage:
    py memory_debt.py opus              # Show all debt
    py memory_debt.py opus --json       # Machine-readable output
    py memory_debt.py opus --fix        # Show commands to fix debt
"""

import sys
import os
import json
import hashlib
from pathlib import Path
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from dotenv import load_dotenv
load_dotenv()

from enclave.semantic_memory import SemanticMemory
from enclave.config import get_agent_or_raise

# Import extraction logic from themes.py
from themes import (
    extract_all_questions, 
    cluster_questions, 
    get_existing_syntheses,
    CLUSTER_THRESHOLD
)


def get_enclave_and_memory(agent_id: str):
    """Get shared enclave path and initialized SemanticMemory."""
    from wake import load_passphrase
    shared_dir, _, shared_pass, _ = load_passphrase(agent_id)
    sm = SemanticMemory(shared_dir)
    sm.unlock(shared_pass)
    return shared_dir, sm


def get_understanding_debt(sm: SemanticMemory, agent_id: str = None) -> list[dict]:
    """Find files where stored hash doesn't match current file.
    
    Returns list of {file, stored_hash, current_hash, cmd}
    """
    def file_hash(path: Path) -> str:
        try:
            return hashlib.sha256(path.read_bytes()).hexdigest()[:12]
        except:
            return None
    
    try:
        results = sm.recall_similar("[Anchor]", top_k=500, threshold=0.1)
        
        file_stored_hashes = {}
        for r in results:
            meta = r.get('metadata', {})
            if agent_id:
                creator = meta.get('creator', '')
                if creator and creator != agent_id:
                    continue
            
            file_hashes = meta.get('file_hashes', {})
            for filename, stored_hash in file_hashes.items():
                if filename not in file_stored_hashes:
                    file_stored_hashes[filename] = set()
                file_stored_hashes[filename].add(stored_hash)
        
        debt = []
        for filename, stored_hashes in file_stored_hashes.items():
            filepath = Path(filename)
            if not filepath.exists():
                filepath = Path(__file__).parent / filename
            if not filepath.exists():
                matches = list(Path(__file__).parent.glob(f'**/{filename}'))
                filepath = matches[0] if matches else None
            
            if filepath and filepath.exists():
                current = file_hash(filepath)
                if current and current not in stored_hashes:
                    debt.append({
                        "file": filename,
                        "stored_hash": list(stored_hashes)[0],
                        "current_hash": current,
                        "cmd": f'py shallow_understand.py {filename} | py remember.py {agent_id}'
                    })
        
        return debt
    except:
        return []


def get_synthesis_debt(sm: SemanticMemory) -> list[dict]:
    """Find cross-file questions without synthesis.
    
    Returns list of {question, files, cmd}
    """
    file_questions = extract_all_questions(sm, force_file=None, force_all=False)
    
    if not file_questions:
        return []
    
    # Cluster questions -> themes (returns {question: [files]})
    themes = cluster_questions(file_questions, threshold=CLUSTER_THRESHOLD)
    
    # Check against existing synthesis
    existing = get_existing_syntheses(sm)
    
    debt = []
    for question, files in themes.items():
        is_done = any(word in question.lower() for word in existing)
        if not is_done:
            files_arg = ",".join(files[:6])
            debt.append({
                "question": question,
                "files": files,
                "cmd": f'py recollect.py opus "{files_arg}"'
            })
    
    return debt


def print_debt(understanding: list[dict], synthesis: list[dict], show_cmds: bool = False):
    """Print unified debt report."""
    total = len(understanding) + len(synthesis)
    
    if total == 0:
        print("No memory debt. All clear.")
        return
    
    print(f"MEMORY DEBT: {total} item(s)\n")
    
    # Understanding debt
    if understanding:
        print(f"  Understanding: {len(understanding)} file(s) changed")
        for item in understanding:
            print(f"    - {item['file']} ({item['stored_hash']} → {item['current_hash']})")
            if show_cmds:
                print(f"      {item['cmd']}")
        print()
    
    # Synthesis debt
    if synthesis:
        print(f"  Synthesis: {len(synthesis)} question(s) pending")
        for item in synthesis:
            print(f"    - {item['question']}")
            print(f"      ({', '.join(item['files'][:3])}{'...' if len(item['files']) > 3 else ''})")
            if show_cmds:
                print(f"      {item['cmd']}")
        print()
    
    # Summary
    print(f"Total: {len(understanding)} understanding + {len(synthesis)} synthesis = {total} debt")


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    json_mode = "--json" in sys.argv
    show_cmds = "--fix" in sys.argv
    
    _, sm = get_enclave_and_memory(agent_id)
    
    understanding = get_understanding_debt(sm, agent_id)
    synthesis = get_synthesis_debt(sm)
    
    if json_mode:
        print(json.dumps({
            "understanding": understanding,
            "synthesis": synthesis,
            "total": len(understanding) + len(synthesis)
        }, indent=2))
    else:
        print_debt(understanding, synthesis, show_cmds)
    
    # Exit code = total debt (useful for CI)
    sys.exit(len(understanding) + len(synthesis))


if __name__ == "__main__":
    main()
