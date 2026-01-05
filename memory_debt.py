#!/usr/bin/env python3
"""
memory_debt.py - Single source of truth for all memory debt.

Memory debt = knowledge not yet committed to semantic memory

Four types (checked in order, fail-early):
  1. Stale debt: files changed since last remember.py
  2. Untracked debt: files with NO understanding stored (learn or delete)
  3. Synthesis debt: cross-file questions without synthesis
  4. Message debt: agent dialogues without synthesis

Usage:
    py memory_debt.py opus              # Fail-early check (shows first failure only)
    py memory_debt.py opus --all        # Show all debt categories
    py memory_debt.py opus --json       # Machine-readable output (all categories)
"""

import sys
import os
import json
import re
import hashlib
from pathlib import Path
from collections import defaultdict
from datetime import datetime

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


def get_untracked_debt(sm: SemanticMemory) -> list[str]:
    """Find .py files with NO understanding stored at all.
    
    These are blind spots - either learn them or delete them.
    Excludes: __pycache__, .venv, test files, __init__.py, enclave/ internals
    
    Returns list of filenames.
    """
    # Get all files that HAVE understanding
    tracked_files = set()
    try:
        results = sm.recall_similar("[Anchor]", top_k=500, threshold=0.1)
        for r in results:
            meta = r.get('metadata', {})
            file_hashes = meta.get('file_hashes', {})
            tracked_files.update(file_hashes.keys())
    except:
        pass
    
    # Scan for all .py files in project root
    project_root = Path(__file__).parent
    untracked = []
    
    # Patterns to exclude
    exclude_patterns = {
        '__pycache__', '.venv', 'venv', '.git', 'node_modules',
        'test_', '_test.py', 'tests/', '__init__.py',
        'enclave/',  # Internal library, not verbs
    }
    
    for py_file in project_root.glob('*.py'):
        filename = py_file.name
        
        # Skip if matches exclusion pattern
        if any(pat in str(py_file) for pat in exclude_patterns):
            continue
        
        # Skip if already tracked
        if filename in tracked_files:
            continue
        
        untracked.append(filename)
    
    return sorted(untracked)


def get_synthesis_debt(sm: SemanticMemory) -> list[dict]:
    """Find cross-file questions without synthesis.
    
    Filters out questions about files that no longer exist.
    
    Returns list of {question, files}
    """
    try:
        from utils.themes import (
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
                # Filter out stale files - only keep files that exist
                valid_files = [f for f in files if _file_exists(f)]
                if valid_files:  # Only add if at least one file still exists
                    debt.append({
                        "question": question,
                        "files": valid_files,
                    })
        
        return debt
    except Exception:
        return []


def _file_exists(filename: str) -> bool:
    """Check if a file exists, trying multiple path resolutions."""
    # Direct path
    if Path(filename).exists():
        return True
    # Relative to project root
    project_root = Path(__file__).parent
    if (project_root / filename).exists():
        return True
    # Glob search (expensive, but catches relocated files)
    matches = list(project_root.glob(f'**/{Path(filename).name}'))
    return len(matches) > 0


def extract_python_definitions(filepath: str) -> list[dict]:
    """Extract function/class definitions with line numbers from a Python file.
    
    Returns list of {name, type, line, signature}
    """
    definitions = []
    try:
        path = Path(filepath)
        if not path.exists():
            path = Path(__file__).parent / filepath
        if not path.exists():
            return []
        
        content = path.read_text(encoding='utf-8')
        lines = content.split('\n')
        
        # Regex for def and class
        def_pattern = re.compile(r'^(\s*)def\s+(\w+)\s*\(([^)]*)\)')
        class_pattern = re.compile(r'^(\s*)class\s+(\w+)')
        
        for i, line in enumerate(lines, 1):
            # Check for function def
            match = def_pattern.match(line)
            if match:
                indent, name, params = match.groups()
                # Skip private methods in summary (but include dunder)
                if name.startswith('_') and not name.startswith('__'):
                    continue
                definitions.append({
                    'name': name,
                    'type': 'def',
                    'line': i,
                    'signature': f"{name}({params[:40]}{'...' if len(params) > 40 else ''})",
                    'indent': len(indent),
                })
                continue
            
            # Check for class
            match = class_pattern.match(line)
            if match:
                indent, name = match.groups()
                definitions.append({
                    'name': name,
                    'type': 'class',
                    'line': i,
                    'signature': name,
                    'indent': len(indent),
                })
    except Exception:
        pass
    
    return definitions


def get_message_debt(sm: SemanticMemory, agent_id: str) -> list[dict]:
    """Find agent dialogues without synthesis.
    
    Returns list of {correspondent, message_count, status, cmd}
    """
    try:
        from utils.msg_synthesis import get_agent_messages, list_synthesis_debt
        conversations = get_agent_messages(agent_id)
        return list_synthesis_debt(agent_id, conversations, sm)
    except Exception:
        return []


# ─────────────────────────────────────────────────────────────────────────────
# Output formatting - fail-early style
# ─────────────────────────────────────────────────────────────────────────────

def format_understanding_debt(debt: list[dict], cross_agent: list[str], untracked: list[str], agent_id: str) -> str:
    """Format understanding debt as actionable SIF template. Returns string."""
    lines = []
    stale = len(debt)
    missing = len(cross_agent)
    blind = len(untracked)
    total = stale + missing + blind
    today = datetime.now().strftime('%Y-%m-%d')
    
    lines.append(f"❌ FAIL - {total} file(s) need understanding")
    lines.append("")
    lines.append(f"@G fix-memory-debt {agent_id} {today}")
    lines.append("")
    
    # STALE files - show what changed and what to cover
    for item in debt:
        filename = item['file']
        safe_slug = filename.replace(".", "-").replace("/", "-").replace("\\", "-")
        lines.append(f"# === {filename} (STALE) ===")
        lines.append(f"N Stale '{filename}' -> hash_changed '{item['stored_hash']} → {item['current_hash']}'")
        
        # Extract definitions if Python file
        if filename.endswith('.py'):
            defs = extract_python_definitions(filename)
            if defs:
                # Show top-level functions (indent 0)
                top_level = [d for d in defs if d['indent'] == 0][:12]
                lines.append(f"# YOU MUST COVER THESE {len(top_level)} FUNCTIONS:")
                for d in top_level:
                    lines.append(f"N Loc '{d['signature']}() ~line {d['line']}'")
        
        lines.append(f"N Cmd 'py remember.py {agent_id} {filename} \"@G {safe_slug} {agent_id} {today}\"'")
        lines.append("")
    
    # MISSING files - partner understands, you don't
    for filename in cross_agent[:5]:
        safe_slug = filename.replace(".", "-").replace("/", "-").replace("\\", "-")
        lines.append(f"# === {filename} (MISSING - partner knows) ===")
        
        if filename.endswith('.py'):
            defs = extract_python_definitions(filename)
            if defs:
                top_level = [d for d in defs if d['indent'] == 0][:12]
                lines.append(f"# YOU MUST COVER THESE {len(top_level)} FUNCTIONS:")
                for d in top_level:
                    lines.append(f"N Loc '{d['signature']}() ~line {d['line']}'")
        
        lines.append(f"N Cmd 'py remember.py {agent_id} {filename} \"@G {safe_slug} {agent_id} {today}\"'")
        lines.append("")
    
    if len(cross_agent) > 5:
        lines.append(f"# ... and {len(cross_agent) - 5} more missing files")
        lines.append("")
    
    # UNTRACKED files - no understanding at all, learn or delete
    if untracked:
        lines.append("# === UNTRACKED FILES ===")
        lines.append("# These files have ZERO understanding stored.")
        lines.append("# Either: 1) Learn them (remember.py) or 2) DELETE them for project density")
        lines.append("# Temporary/experimental files should not linger.")
        lines.append("")
        
        for filename in untracked[:8]:
            safe_slug = filename.replace(".", "-").replace("/", "-").replace("\\", "-")
            lines.append(f"# {filename} - UNTRACKED (learn or delete)")
            
            if filename.endswith('.py'):
                defs = extract_python_definitions(filename)
                if defs:
                    top_level = [d for d in defs if d['indent'] == 0][:6]
                    if top_level:
                        lines.append(f"#   Functions: {', '.join(d['name'] for d in top_level)}")
            
            lines.append(f"N Choice '{filename}' -> learn 'py remember.py {agent_id} {filename}' OR delete 'rm {filename}'")
            lines.append("")
        
        if len(untracked) > 8:
            lines.append(f"# ... and {len(untracked) - 8} more untracked files")
            lines.append("")
    
    # Template showing expected depth
    lines.append("# === TEMPLATE: What GOOD understanding looks like ===")
    lines.append("# READ THE WHOLE FILE. No skimming. Cover every function.")
    lines.append("N S 'One-line: what this file IS'")
    lines.append("N P 'WHY it exists - what problem it solves'")
    lines.append("N Flow 'main() → helper1() → helper2()'  # execution order")
    lines.append("N Loc 'key_function() ~line 42' -> implements 'core behavior'")
    lines.append("N Loc 'another_func() ~line 89' -> handles 'edge case X'")
    lines.append("N D 'Design choice: why X not Y'")
    lines.append("N G 'Gotcha: what breaks and when' -> warns _-1")
    lines.append("N M 'Metric: concrete number if relevant'")
    lines.append("E _S contains _Flow")
    lines.append("")
    lines.append("# NODE TYPES: S=Summary P=Purpose C=Component D=Design G=Gotcha")
    lines.append("#             I=Insight M=Metric Loc=Location Flow=Execution")
    
    return '\n'.join(lines)


def format_synthesis_debt(debt: list[dict], agent_id: str) -> str:
    """Format synthesis debt as actionable SIF template. Returns string."""
    lines = []
    today = datetime.now().strftime('%Y-%m-%d')
    
    lines.append(f"❌ FAIL - {len(debt)} theme(s) need synthesis")
    lines.append("")
    lines.append(f"@G fix-synthesis-debt {agent_id} {today}")
    lines.append("")
    
    for i, item in enumerate(debt[:5], 1):
        theme_slug = item['question'][:40].replace(' ', '-').replace('?', '').lower()
        files = item['files'][:4]
        
        lines.append(f"# === Theme {i}: {item['question'][:60]} ===")
        lines.append(f"N Theme '{item['question']}'")
        for f in files:
            lines.append(f"N SourceFile '{f}'")
        lines.append(f"N Cmd 'py recall.py {agent_id} \"{' '.join(files)}\"'  # gather context")
        lines.append(f"N Cmd 'py remember.py {agent_id} --theme \"{theme_slug}\" \"@G {theme_slug} {agent_id} {today}\"'")
        lines.append("")
    
    if len(debt) > 5:
        lines.append(f"# ... and {len(debt) - 5} more themes")
        lines.append("")
    
    lines.append("# === TEMPLATE: Theme synthesis format ===")
    lines.append("N S 'Cross-file insight that emerges from comparing sources'")
    lines.append("N Pattern 'What pattern appears across files'")
    lines.append("N Tension 'Where files disagree or contradict'")
    lines.append("N I 'Novel understanding from juxtaposition'")
    lines.append("E _S synthesizes SourceFile1 SourceFile2")
    
    return '\n'.join(lines)


def format_message_debt(debt: list[dict], agent_id: str) -> str:
    """Format message debt. Returns string."""
    lines = []
    total_msgs = sum(d['message_count'] for d in debt)
    lines.append(f"❌ FAIL - {len(debt)} dialogue(s) need synthesis ({total_msgs} total messages)")
    lines.append("")
    
    for item in debt:
        status = "stale" if item['status'] == 'stale' else "none"
        lines.append(f"  {item['correspondent']}: {item['message_count']} msgs ({status})")
    lines.append("")
    
    lines.append("TO FIX:")
    for item in debt:
        lines.append(f"  py remember.py {agent_id} --dialogue {item['correspondent']}")
    
    return '\n'.join(lines)


def print_all_debt(understanding: list[dict], cross_agent: list[str], untracked: list[str],
                   synthesis: list[dict], messages: list[dict], agent_id: str):
    """Print all debt categories (--all mode)."""
    total = len(understanding) + len(cross_agent) + len(untracked) + len(synthesis) + len(messages)
    
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
    
    if untracked:
        print(f"\n❌ FAIL - {len(untracked)} file(s) UNTRACKED (learn or delete):")
        for f in untracked[:8]:
            print(f"  {f} - either: py remember.py {agent_id} {f} OR rm {f}")
        if len(untracked) > 8:
            print(f"  ... and {len(untracked) - 8} more")
    
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
    
    # Show SIF format hint at bottom
    print()
    print("SIF format: N <Type> '<content>' -> <relation> <target>")
    print("Types: S=Synthesis P=Purpose C=Component D=Design G=Gotcha I=Insight")


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
    untracked = get_untracked_debt(sm)
    synthesis = get_synthesis_debt(sm)
    messages = get_message_debt(sm, agent_id)
    
    total = len(understanding) + len(cross_agent) + len(untracked) + len(synthesis) + len(messages)
    
    if json_mode:
        print(json.dumps({
            "understanding": understanding,
            "cross_agent": cross_agent,
            "untracked": untracked,
            "synthesis": synthesis,
            "messages": messages,
            "total": total
        }, indent=2))
        sys.exit(total)
    
    if total == 0:
        print("✅ No memory debt")
        sys.exit(0)
    
    if all_mode:
        print_all_debt(understanding, cross_agent, untracked, synthesis, messages, agent_id)
        sys.exit(total)
    
    # Fail-early: show only the first category with debt
    if understanding or cross_agent or untracked:
        print(format_understanding_debt(understanding, cross_agent, untracked, agent_id))
        sys.exit(len(understanding) + len(cross_agent) + len(untracked))
    
    if synthesis:
        print(format_synthesis_debt(synthesis, agent_id))
        sys.exit(len(synthesis))
    
    if messages:
        print(format_message_debt(messages, agent_id))
        sys.exit(len(messages))


if __name__ == "__main__":
    main()
