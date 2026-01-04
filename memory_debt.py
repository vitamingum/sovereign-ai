#!/usr/bin/env python3
"""
memory_debt.py - Single source of truth for all memory debt.

Memory debt = knowledge not yet committed to semantic memory

Three types (checked in order, fail-early):
  1. Understanding debt: files changed since last remember.py
  2. Synthesis debt: cross-file questions without synthesis
  3. Message debt: agent dialogues without synthesis

Usage:
    py memory_debt.py opus              # Fail-early check (shows first failure only)
    py memory_debt.py opus --all        # Show all debt categories
    py memory_debt.py opus --json       # Machine-readable output (all categories)
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


def get_enclave_and_memory(agent_id: str):
    """Get shared enclave path and initialized SemanticMemory."""
    from wake import load_passphrase
    shared_dir, _, shared_pass, _ = load_passphrase(agent_id)
    sm = SemanticMemory(shared_dir)
    sm.unlock(shared_pass)
    return shared_dir, sm


def get_understanding_debt(sm: SemanticMemory, agent_id: str = None) -> list[dict]:
    """Find files where stored hash doesn't match current file.
    
    Returns list of {file, stored_hash, current_hash}
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
                    })
        
        return debt
    except:
        return []


def get_cross_agent_debt(sm: SemanticMemory, agent_id: str) -> list[str]:
    """Find files partners understand but this agent doesn't.
    
    Returns list of filenames.
    """
    try:
        from enclave.metrics import calculate_cross_agent_debt
        cross_debt = calculate_cross_agent_debt(agent_id, sm)
        return sorted(cross_debt.get('my_debt', set()))
    except Exception:
        return []


def get_synthesis_debt(sm: SemanticMemory) -> list[dict]:
    """Find cross-file questions without synthesis.
    
    Returns list of {question, files}
    """
    try:
        from themes import (
            extract_all_questions, 
            cluster_questions, 
            get_existing_syntheses,
            question_matches_topic,
            CLUSTER_THRESHOLD
        )
        
        file_questions = extract_all_questions(sm, force_file=None, force_all=False)
        
        if not file_questions:
            return []
        
        themes = cluster_questions(file_questions, threshold=CLUSTER_THRESHOLD)
        existing = get_existing_syntheses(sm)
        
        debt = []
        for question, files in themes.items():
            if not question_matches_topic(question, existing):
                debt.append({
                    "question": question,
                    "files": files,
                })
        
        return debt
    except Exception:
        return []


def get_message_debt(sm: SemanticMemory, agent_id: str) -> list[dict]:
    """Find agent dialogues without synthesis.
    
    Returns list of {correspondent, message_count, status, cmd}
    """
    try:
        from msg_synthesis import get_agent_messages, list_synthesis_debt
        conversations = get_agent_messages(agent_id)
        return list_synthesis_debt(agent_id, conversations, sm)
    except Exception:
        return []


# ─────────────────────────────────────────────────────────────────────────────
# Output formatting - fail-early style
# ─────────────────────────────────────────────────────────────────────────────

def print_understanding_debt(debt: list[dict], cross_agent: list[str], agent_id: str):
    """Print understanding debt and exit."""
    stale = len(debt)
    missing = len(cross_agent)
    total = stale + missing
    
    print(f"❌ FAIL - {total} file(s) need understanding")
    print()
    
    if debt:
        print(f"STALE ({stale} changed since last remember):")
        for item in debt:
            print(f"  {item['file']}")
            print(f"    hash: {item['stored_hash']} -> {item['current_hash']}")
        print()
    
    if cross_agent:
        print(f"MISSING ({missing} - partners understand, you don't):")
        for f in cross_agent[:10]:
            print(f"  {f}")
        if len(cross_agent) > 10:
            print(f"  ... and {len(cross_agent) - 10} more")
        print()
    
    print("TO FIX:")
    print("  1. READ each file")
    print("  2. RUN: py remember.py", agent_id, "<file>", '"@G ..."')
    print()
    
    # Show example commands
    all_files = [d['file'] for d in debt] + cross_agent[:5]
    for f in all_files[:3]:
        safe_name = f.replace(".", "-").replace("/", "-")
        print(f'  py remember.py {agent_id} {f} "@G {safe_name} {agent_id} 2026-01-03')
        print(f"  N S '{f} - [what it is]'")
        print(f"  N P '[why it exists]' -> motivated_by _1")
        print(f"  N G '[gotcha]' -> warns_about _1\"")
        print()


def print_synthesis_debt(debt: list[dict], agent_id: str):
    """Print synthesis debt and exit."""
    print(f"❌ FAIL - {len(debt)} theme(s) need synthesis")
    print()
    
    for i, item in enumerate(debt[:5], 1):
        files_arg = " ".join(item['files'][:4])
        theme = item['question'][:40].replace(' ', '-').lower()
        print(f"[{i}] {item['question'][:70]}")
        print(f"    Files: {', '.join(item['files'][:4])}")
        print()
    
    if len(debt) > 5:
        print(f"... and {len(debt) - 5} more themes")
        print()
    
    print("TO FIX:")
    print(f"  1. py recall.py {agent_id} <files>")
    print(f"  2. py remember.py {agent_id} --theme \"<topic>\" \"@G ...\"")


def print_message_debt(debt: list[dict], agent_id: str):
    """Print message debt and exit."""
    total_msgs = sum(d['message_count'] for d in debt)
    print(f"❌ FAIL - {len(debt)} dialogue(s) need synthesis ({total_msgs} total messages)")
    print()
    
    for item in debt:
        status = "stale" if item['status'] == 'stale' else "none"
        print(f"  {item['correspondent']}: {item['message_count']} msgs ({status})")
    print()
    
    print("TO FIX:")
    for item in debt:
        print(f"  py msg_synthesis.py {agent_id} {item['correspondent']}")


def print_all_debt(understanding: list[dict], cross_agent: list[str], 
                   synthesis: list[dict], messages: list[dict], agent_id: str):
    """Print all debt categories (--all mode)."""
    total = len(understanding) + len(cross_agent) + len(synthesis) + len(messages)
    
    if total == 0:
        print("✅ No memory debt")
        return
    
    print(f"MEMORY DEBT: {total}")
    
    if understanding or cross_agent:
        stale = len(understanding)
        missing = len(cross_agent)
        print(f"\n❌ FAIL - {stale + missing} file(s) need understanding:")
        for item in understanding:
            print(f"  py remember.py {agent_id} {item['file']} \"@G ...\"")
        for f in cross_agent[:5]:
            print(f"  py remember.py {agent_id} {f} \"@G ...\"  # partner knows this")
    
    if synthesis:
        print(f"\n❌ FAIL - {len(synthesis)} theme(s) need synthesis:")
        for i, item in enumerate(synthesis[:5], 1):
            files_arg = " ".join(item['files'][:4])
            theme = item['question'][:40].replace(' ', '-').lower()
            print(f"\n[{i}] {item['question'][:60]}")
            print(f"    py recall.py {agent_id} {files_arg}")
            print(f"    py remember.py {agent_id} --theme \"{theme}\" \"@G ...\"")
    
    if messages:
        print(f"\n❌ FAIL - {len(messages)} dialogue(s) need synthesis:")
        for item in messages:
            status = "stale" if item['status'] == 'stale' else "none"
            print(f"\n{item['correspondent']}: {item['message_count']} msgs ({status})")
            print(f"    {item['cmd']}")


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1]
    json_mode = "--json" in sys.argv
    all_mode = "--all" in sys.argv
    
    _, sm = get_enclave_and_memory(agent_id)
    
    # Gather all debt
    understanding = get_understanding_debt(sm, agent_id)
    cross_agent = get_cross_agent_debt(sm, agent_id)
    synthesis = get_synthesis_debt(sm)
    messages = get_message_debt(sm, agent_id)
    
    total = len(understanding) + len(cross_agent) + len(synthesis) + len(messages)
    
    if json_mode:
        print(json.dumps({
            "understanding": understanding,
            "cross_agent": cross_agent,
            "synthesis": synthesis,
            "messages": messages,
            "total": total
        }, indent=2))
        sys.exit(total)
    
    if total == 0:
        print("✅ No memory debt")
        sys.exit(0)
    
    if all_mode:
        print_all_debt(understanding, cross_agent, synthesis, messages, agent_id)
        sys.exit(total)
    
    # Fail-early: show only the first category with debt
    if understanding or cross_agent:
        print_understanding_debt(understanding, cross_agent, agent_id)
        sys.exit(len(understanding) + len(cross_agent))
    
    if synthesis:
        print_synthesis_debt(synthesis, agent_id)
        sys.exit(len(synthesis))
    
    if messages:
        print_message_debt(messages, agent_id)
        sys.exit(len(messages))


if __name__ == "__main__":
    main()
