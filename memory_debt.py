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
        # Use list_all() to scan ALL memories, not similarity search
        # This ensures we find recent memories regardless of their embedding similarity
        results = sm.list_all()
        
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
            # Don't glob search - if file moved, it's a different file
            # Understanding for "dream.py" shouldn't match "research/dream.py"
            if not filepath.exists():
                continue  # File deleted or moved - not debt, just orphaned understanding
            
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
        # Scan ALL memories - don't use similarity search which may miss recent entries
        results = sm.list_all()
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
    
    lines.append(f"❌ {agent_id.capitalize()}: {total} files need your understanding NOW")
    lines.append(f"@G fix-debt {agent_id} {today}")
    lines.append("")
    
    # Collect all files into categories
    stale_files = [item['file'] for item in debt]
    
    # List files by category (collapsed)
    if stale_files:
        lines.append(f"N Stale '{', '.join(stale_files)}'")
    if cross_agent:
        lines.append(f"N Missing '{', '.join(cross_agent[:10])}'{'...' if len(cross_agent) > 10 else ''}")
    if untracked:
        lines.append(f"N Untracked '{', '.join(untracked[:10])}'{'...' if len(untracked) > 10 else ''}")
        lines.append("# ^ UNTRACKED = learn OR delete (temp files should not linger)")
    lines.append("")
    
    # Pick ONE example file (prefer stale, then missing, then untracked)
    example_file = None
    example_type = None
    if debt:
        example_file = debt[0]['file']
        example_type = "STALE"
    elif cross_agent:
        example_file = cross_agent[0]
        example_type = "MISSING"
    elif untracked:
        example_file = untracked[0]
        example_type = "UNTRACKED"
    
    if example_file:
        safe_slug = example_file.replace(".", "-").replace("/", "-").replace("\\", "-")
        lines.append(f"# HOW TO FIX ({example_type}: {example_file}):")
        
        # Show 2 example Loc nodes if Python file
        if example_file.endswith('.py'):
            defs = extract_python_definitions(example_file)
            if defs:
                top_level = [d for d in defs if d['indent'] == 0][:2]
                for d in top_level:
                    lines.append(f"N Loc '{d['signature']} ~line {d['line']}'")
                if len([d for d in defs if d['indent'] == 0]) > 2:
                    lines.append(f"# ... cover ALL {len([d for d in defs if d['indent'] == 0])} functions")
        
        lines.append("N S 'What this file IS'")
        lines.append("N P 'WHY it exists'")
        lines.append("N D 'A key design decision'")
        lines.append("N G 'A gotcha or risk'")
        lines.append("E _1 implements _2")
        lines.append("E _3 justifies _1")
        lines.append("E _4 warns_about _3")
        lines.append(f"N Cmd 'py remember.py {agent_id} {example_file} @understanding.sif'")
    
    return '\n'.join(lines)


def format_synthesis_debt(debt: list[dict], agent_id: str) -> str:
    """Format synthesis debt as actionable SIF template. Returns string."""
    lines = []
    today = datetime.now().strftime('%Y-%m-%d')
    
    # Collect all theme names
    themes = [item['question'][:40] for item in debt[:8]]
    
    lines.append(f"❌ {agent_id.capitalize()}: {len(debt)} themes need your synthesis")
    lines.append(f"@G fix-synthesis {agent_id} {today}")
    lines.append("")
    lines.append(f"N Themes '{', '.join(themes)}'{'...' if len(debt) > 8 else ''}")
    lines.append("")
    
    # Show ONE example
    if debt:
        item = debt[0]
        theme_slug = item['question'][:40].replace(' ', '-').replace('?', '').lower()
        files = item['files'][:3]
        
        lines.append(f"# HOW TO FIX ({item['question'][:50]}):")
        lines.append(f"N I 'Cross-file insight about {theme_slug}'")
        lines.append(f"N D 'WHY these files share this pattern'")
        lines.append(f"N Cmd 'py remember.py {agent_id} --theme \"{theme_slug}\" @synthesis.sif'")
    
    return '\n'.join(lines)


def format_message_debt(debt: list[dict], agent_id: str) -> str:
    """Format message debt. Returns string."""
    lines = []
    total_msgs = sum(d['message_count'] for d in debt)
    lines.append(f"❌ {agent_id.capitalize()}: {len(debt)} dialogues need your synthesis ({total_msgs} msgs)")
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
    """Print all debt categories (--all mode) - concise summary."""
    total = len(understanding) + len(cross_agent) + len(untracked) + len(synthesis) + len(messages)
    
    if total == 0:
        print(f"✅ {agent_id.capitalize()}: no memory debt")
        return
    
    print(f"❌ {agent_id.capitalize()}: {total} items need your attention")
    
    # Understanding debt (collapsed)
    stale_files = [item['file'] for item in understanding]
    if stale_files:
        print(f"N Stale '{', '.join(stale_files[:5])}'{'...' if len(stale_files) > 5 else ''}")
    if cross_agent:
        print(f"N Missing '{', '.join(cross_agent[:5])}'{'...' if len(cross_agent) > 5 else ''}")
    if untracked:
        print(f"N Untracked '{', '.join(untracked[:5])}'{'...' if len(untracked) > 5 else ''}")
        print("# ^ learn OR delete")
    
    # Synthesis debt (collapsed)
    if synthesis:
        themes = [item['question'][:30] for item in synthesis[:5]]
        print(f"N Themes '{', '.join(themes)}'{'...' if len(synthesis) > 5 else ''}")
    
    # Message debt (collapsed)
    if messages:
        correspondents = [item['correspondent'] for item in messages]
        print(f"N Dialogues '{', '.join(correspondents)}'")
    
    print("")
    print(f"N Cmd 'py memory_debt.py {agent_id}'  # fail-early details")


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
