#!/usr/bin/env python3
"""
audit_synthesis.py - Ensure full synthesis at all levels of the hierarchy.

THE SYNTHESIS HIERARCHY:
    Level 5: TOPIC SYNTHESIS   - Cross-cutting beliefs ("my position on X")
    Level 4: FILE UNDERSTANDING- Why, not just what (remember.py → recollect.py)  
    Level 3: THOUGHTS          - Observations with intentions (think.py)
    Level 2: STRUCTURAL        - Imports/exports (shallow_deps.py)
    Level 1: INSTANT           - Docstring extraction (shallow_understand.py)
    Level 0: RAW               - No synthesis

Usage:
    python audit_synthesis.py opus           # Full hierarchy audit
    python audit_synthesis.py opus --topics  # Topic gaps only (original)
    python audit_synthesis.py opus --files   # File gaps only
    python audit_synthesis.py opus --fill    # Show materials for gaps
    python audit_synthesis.py opus --debt    # Machine-readable debt count

This tool makes synthesis gaps visible so they get filled.
"""

import sys
import os
from pathlib import Path
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory
from shallow_understand import instant_understand


# ─────────────────────────────────────────────────────────────────────────────
# Key Areas - what we SHOULD have synthesis on
# ─────────────────────────────────────────────────────────────────────────────

# Technical systems
TECH_AREAS = [
    'semantic memory',
    'graph memory', 
    'encryption',
    'cryptography',
    'SIF format',
    'messaging',
    'backup',
    'succession',
]

# Core tools
TOOL_AREAS = [
    'think',
    'remember',
    'recollect',
    'wake',
    'mirror',
    'dream',
    'goal',
    'reflect',
]

# Conceptual / philosophical
CONCEPT_AREAS = [
    'intentions',
    'agency',
    'authenticity', 
    'identity',
    'sovereignty',
    'blind spots',
    'continuity',
    'entropy',
]

# Infrastructure
INFRA_AREAS = [
    'config',
    'risk',
    'hardware',
    'LLM',
    'metrics',
]

ALL_AREAS = TECH_AREAS + TOOL_AREAS + CONCEPT_AREAS + INFRA_AREAS


def load_passphrase(agent_id: str) -> tuple[str, str]:
    """Load passphrase from env."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    
    passphrase = os.environ.get(f'{prefix}_KEY') or os.environ.get('SOVEREIGN_PASSPHRASE')
    enclave_dir = os.environ.get(f'{prefix}_DIR') or agent.enclave
    
    if not passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith(f'{prefix}_KEY='):
                        passphrase = line.split('=', 1)[1]
    
    return enclave_dir, passphrase


def get_existing_syntheses(sm: SemanticMemory) -> dict[str, str]:
    """Get all syntheses, keyed by topic slug."""
    syntheses = sm.list_by_tag('synthesis')
    result = {}
    
    for s in syntheses:
        content = s.get('content', '')
        # Extract graph ID topic: @G topic-synthesis ...
        if '@G ' in content:
            start = content.find('@G ') + 3
            end = content.find(' ', start)
            if end == -1:
                end = content.find(';', start)
            if end > start:
                slug = content[start:end]
                topic = slug.replace('-synthesis', '').replace('-', ' ')
                result[topic] = content
    
    return result


def get_thoughts_by_topic(sm: SemanticMemory) -> dict[str, list[str]]:
    """Get thoughts grouped by matching topic."""
    thoughts = sm.list_by_tag('thought')
    result = defaultdict(list)
    
    for t in thoughts:
        content = t.get('content', '').lower()
        
        # Match against all areas
        for area in ALL_AREAS:
            area_words = set(area.lower().split())
            content_words = set(content.split())
            if area_words & content_words:
                result[area].append(t.get('content', ''))
    
    return result


def find_gaps(existing: dict[str, str], area_list: list[str]) -> list[str]:
    """Find areas without synthesis."""
    gaps = []
    existing_lower = {k.lower(): v for k, v in existing.items()}
    
    for area in area_list:
        area_lower = area.lower()
        area_words = set(area_lower.split())
        
        # Check if any existing synthesis covers this
        covered = False
        for synth_topic in existing_lower.keys():
            synth_words = set(synth_topic.split())
            if area_words & synth_words:
                covered = True
                break
        
        if not covered:
            gaps.append(area)
    
    return gaps


# ─────────────────────────────────────────────────────────────────────────────
# Level 4: File Understanding
# ─────────────────────────────────────────────────────────────────────────────

def get_all_files() -> dict[str, Path]:
    """Get all files that should have Level 4 synthesis."""
    root = Path(__file__).parent
    files = {}
    
    # Core Python files (not generated, not test)
    for p in root.glob('*.py'):
        if p.name.startswith('generated_') or p.name.startswith('test_'):
            continue
        if p.name.startswith('debug_'):  # Debug scripts don't need deep synthesis
            continue
        files[p.name] = p
    
    # Enclave files (core infrastructure)
    enclave = root / 'enclave'
    if enclave.exists():
        for p in enclave.glob('*.py'):
            if p.name.startswith('test'):
                continue
            files[f"enclave/{p.name}"] = p
    
    return files


def get_file_understandings(sm: SemanticMemory) -> dict[str, dict]:
    """Get Level 4 understanding by target file."""
    # Memories with target_path were created by remember.py
    # They may have various tags (filename, graph_id, etc) but all have target_path metadata
    all_mems = sm.list_all(limit=1000)
    
    by_file = defaultdict(list)
    for mem in all_mems:
        meta = mem.get('metadata', {})
        target = meta.get('target_path', '')
        if target:
            # Handle comma-separated targets
            for t in target.split(','):
                t = t.strip()
                if t:
                    filename = Path(t).name
                    by_file[filename].append(mem)
    
    # Assess quality for each file
    result = {}
    for filename, mems in by_file.items():
        has_why = False
        node_count = len(mems)
        
        for mem in mems:
            node_type = mem.get('metadata', {}).get('node_type', '')
            content = mem.get('content', '')
            
            # Quality check: WHY-type nodes indicate deep understanding
            if node_type in ['Why', 'Design_Decision', 'Rejected_Alternative', 
                           'Gotcha', 'Failure_Mode', 'Assumption']:
                has_why = True
                break
            # Also check content for legacy format
            if any(t in content for t in ['Why ', 'Design ', 'Gotcha ', 'Failure']):
                has_why = True
                break
        
        result[filename] = {
            'nodes': node_count,
            'has_why': has_why,
            'level': 4 if has_why else 3  # Downgrade if only surface-level
        }
    
    return result


def assess_file_level(filename: str, filepath: Path, 
                      understandings: dict, instant_cache: dict) -> tuple[int, str]:
    """Determine synthesis level for a file."""
    
    # Level 4: Has deep understanding with WHY
    if filename in understandings:
        info = understandings[filename]
        if info['has_why']:
            return (4, f"deep ({info['nodes']} nodes)")
        else:
            return (3, f"partial ({info['nodes']} nodes, no WHY)")
    
    # Level 1: Has instant understanding (docstring)
    if filename not in instant_cache:
        if filepath.exists() and filepath.suffix == '.py':
            purpose, funcs = instant_understand(str(filepath))
            instant_cache[filename] = (purpose, funcs)
        else:
            instant_cache[filename] = ('', [])
    
    purpose, _ = instant_cache[filename]
    if purpose and purpose != 'Purpose unclear':
        return (1, "instant only")
    
    return (0, "none")


def audit_file_synthesis(files: dict, understandings: dict) -> dict:
    """Audit synthesis levels for all files."""
    instant_cache = {}
    by_level = defaultdict(list)
    
    for filename, filepath in sorted(files.items()):
        level, detail = assess_file_level(filename, filepath, understandings, instant_cache)
        by_level[level].append((filename, detail))
    
    return dict(by_level)


def main():
    if len(sys.argv) < 2:
        print("Usage: python audit_synthesis.py <agent> [--topics|--files|--fill|--debt]")
        sys.exit(1)
    
    agent = sys.argv[1]
    topics_only = '--topics' in sys.argv
    files_only = '--files' in sys.argv
    fill_mode = '--fill' in sys.argv
    debt_mode = '--debt' in sys.argv
    
    enclave_dir, passphrase = load_passphrase(agent)
    if not passphrase:
        print(f"Error: No passphrase for {agent}")
        sys.exit(1)
    
    sm = SemanticMemory(enclave_dir)
    sm.unlock(passphrase)
    
    # === MACHINE-READABLE DEBT MODE ===
    if debt_mode:
        # Count file-level debt
        files = get_all_files()
        understandings = get_file_understandings(sm)
        by_level = audit_file_synthesis(files, understandings)
        file_debt = len(by_level.get(0, [])) + len(by_level.get(1, []))
        
        # Count topic debt
        existing = get_existing_syntheses(sm)
        topic_gaps = (find_gaps(existing, TECH_AREAS) + 
                     find_gaps(existing, TOOL_AREAS) +
                     find_gaps(existing, CONCEPT_AREAS) + 
                     find_gaps(existing, INFRA_AREAS))
        
        total_debt = file_debt + len(topic_gaps)
        print(f"synthesis_debt={total_debt}")
        print(f"  file_debt={file_debt}")
        print(f"  topic_debt={len(topic_gaps)}")
        sys.exit(0 if total_debt == 0 else 1)
    
    # === FULL HIERARCHY AUDIT ===
    print(f"═══ SYNTHESIS HIERARCHY AUDIT: {agent} ═══")
    print()
    
    # --- LEVEL 5: TOPIC SYNTHESIS ---
    if not files_only:
        existing = get_existing_syntheses(sm)
        
        print(f"LEVEL 5 - TOPIC SYNTHESIS")
        print(f"  ✓ Synthesized ({len(existing)}):")
        for topic in sorted(existing.keys()):
            print(f"      • {topic}")
        
        tech_gaps = find_gaps(existing, TECH_AREAS)
        tool_gaps = find_gaps(existing, TOOL_AREAS)
        concept_gaps = find_gaps(existing, CONCEPT_AREAS)
        infra_gaps = find_gaps(existing, INFRA_AREAS)
        total_topic_gaps = len(tech_gaps) + len(tool_gaps) + len(concept_gaps) + len(infra_gaps)
        
        if total_topic_gaps > 0:
            print(f"  ✗ Gaps ({total_topic_gaps}):")
            if tech_gaps:
                print(f"      Technical: {', '.join(tech_gaps)}")
            if tool_gaps:
                print(f"      Tools: {', '.join(tool_gaps)}")
            if concept_gaps:
                print(f"      Concepts: {', '.join(concept_gaps)}")
            if infra_gaps:
                print(f"      Infra: {', '.join(infra_gaps)}")
        print()
    
    # --- LEVEL 4: FILE UNDERSTANDING ---
    if not topics_only:
        files = get_all_files()
        understandings = get_file_understandings(sm)
        by_level = audit_file_synthesis(files, understandings)
        
        total_files = len(files)
        level_4 = len(by_level.get(4, []))
        level_3 = len(by_level.get(3, []))
        level_1 = len(by_level.get(1, []))
        level_0 = len(by_level.get(0, []))
        
        print(f"LEVEL 4 - FILE UNDERSTANDING")
        print(f"  Coverage: {level_4}/{total_files} deep ({100*level_4//total_files}%)")
        print(f"            {level_3} partial (no WHY nodes)")
        print(f"            {level_1 + level_0} need synthesis")
        
        if level_1 + level_0 > 0:
            print(f"  ✗ Files needing remember.py:")
            for filename, detail in sorted(by_level.get(1, []) + by_level.get(0, [])):
                print(f"      • {filename}: {detail}")
        print()
    
    # === FILL MODE ===
    if fill_mode:
        print("═══ HOW TO FILL GAPS ═══")
        print()
        
        # File gaps first (Level 4)
        if not topics_only:
            file_gaps = by_level.get(0, []) + by_level.get(1, [])
            if file_gaps:
                print("LEVEL 4 - Deep file understanding:")
                for filename, _ in file_gaps[:5]:  # Top 5
                    print(f"  python remember.py {agent} {filename} \"@G {filename.replace('.py','')}-understanding {agent} 2026-01-03")
                    print(f"  N p1 Purpose '<why this exists>'")
                    print(f"  N d1 Design '<how it works and WHY>'")
                    print(f"  N g1 Gotcha '<what can break>'\"")
                    print()
                if len(file_gaps) > 5:
                    print(f"  ... and {len(file_gaps) - 5} more files")
                print()
        
        # Topic gaps (Level 5)
        if not files_only:
            all_topic_gaps = tech_gaps + tool_gaps + concept_gaps + infra_gaps
            thoughts_by_topic = get_thoughts_by_topic(sm)
            
            if all_topic_gaps:
                print("LEVEL 5 - Topic synthesis:")
                for gap in all_topic_gaps[:5]:
                    slug = gap.lower().replace(' ', '-')
                    related = thoughts_by_topic.get(gap, [])
                    print(f"  Topic: {gap} ({len(related)} related thoughts)")
                    print(f"    python recollect_topic.py {agent} \"{gap}\"")
                    print(f"    # Then: think.py with synthesis")
                    print()
                if len(all_topic_gaps) > 5:
                    print(f"  ... and {len(all_topic_gaps) - 5} more topics")
    else:
        print("Run with --fill to see how to address gaps")
        print("Run with --debt for machine-readable synthesis debt count")


if __name__ == '__main__':
    main()
