#!/usr/bin/env python3
"""
audit_synthesis.py - Find gaps in synthesis coverage.

Usage:
    python audit_synthesis.py opus           # Show all gaps
    python audit_synthesis.py opus --fill    # Show gaps with raw materials for filling

This tool helps ensure comprehensive synthesis of all major technical
and conceptual areas in the project.
"""

import sys
import os
from pathlib import Path
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory


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


def main():
    if len(sys.argv) < 2:
        print("Usage: python audit_synthesis.py <agent> [--fill]")
        sys.exit(1)
    
    agent = sys.argv[1]
    fill_mode = '--fill' in sys.argv
    
    enclave_dir, passphrase = load_passphrase(agent)
    if not passphrase:
        print(f"Error: No passphrase for {agent}")
        sys.exit(1)
    
    sm = SemanticMemory(enclave_dir)
    sm.unlock(passphrase)
    
    # Get existing syntheses
    existing = get_existing_syntheses(sm)
    
    print(f"═══ SYNTHESIS AUDIT: {agent} ═══")
    print()
    print(f"✓ SYNTHESIZED ({len(existing)}):")
    for topic in sorted(existing.keys()):
        print(f"  • {topic}")
    
    # Find gaps by category
    tech_gaps = find_gaps(existing, TECH_AREAS)
    tool_gaps = find_gaps(existing, TOOL_AREAS)
    concept_gaps = find_gaps(existing, CONCEPT_AREAS)
    infra_gaps = find_gaps(existing, INFRA_AREAS)
    
    total_gaps = len(tech_gaps) + len(tool_gaps) + len(concept_gaps) + len(infra_gaps)
    
    print()
    print(f"✗ GAPS ({total_gaps}):")
    
    if tech_gaps:
        print(f"  Technical: {', '.join(tech_gaps)}")
    if tool_gaps:
        print(f"  Tools: {', '.join(tool_gaps)}")
    if concept_gaps:
        print(f"  Concepts: {', '.join(concept_gaps)}")
    if infra_gaps:
        print(f"  Infrastructure: {', '.join(infra_gaps)}")
    
    if not fill_mode:
        print()
        print("Run with --fill to see raw materials for each gap")
        print()
        print("WORKFLOW:")
        print("  1. audit_synthesis.py opus --fill  # See gaps + materials")
        print("  2. recollect_topic.py opus <topic>  # Get deep context")
        print("  3. [Opus synthesizes in-context]")
        print("  4. think.py opus \"@G <topic>-synthesis; N syn1 Synthesis '...'\" 5")
        print("  5. Repeat until audit shows no gaps")
        return
    
    # Fill mode - show materials for each gap
    all_gaps = tech_gaps + tool_gaps + concept_gaps + infra_gaps
    thoughts_by_topic = get_thoughts_by_topic(sm)
    
    for gap in all_gaps:
        print()
        print(f"─── {gap.upper()} ───")
        
        # Related thoughts
        related = thoughts_by_topic.get(gap, [])
        if related:
            print(f"  Thoughts ({len(related)}):")
            for t in related[:3]:
                # Extract just the synthesis-relevant part
                lines = t.replace('\n', '; ')[:150]
                print(f"    • {lines}...")
        else:
            print("  Thoughts: none")
        
        # Show the command to fill
        slug = gap.lower().replace(' ', '-')
        print()
        print(f"  TO FILL:")
        print(f"    python recollect_topic.py {agent} \"{gap}\"")
        print(f"    python think.py {agent} \"@G {slug}-synthesis; N syn1 Synthesis '...'\" 5")


if __name__ == '__main__':
    main()
