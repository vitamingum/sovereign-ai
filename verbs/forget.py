#!/usr/bin/env python3
"""
forget.py - release what no longer serves

    source: forget.三語
    compiler: merged
    date: 2026-01-20

        destruction requires intent
        garbage doesn't serve sovereignty
        
                        間委 → 間主
"""

import sys
import os
import argparse
import fnmatch
from pathlib import Path

# Ensure project root in path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from lib_enclave.sovereign_agent import SovereignAgent

def normalize_topic(topic: str) -> str:
    """Normalize topic for matching (handle hyphen/underscore)."""
    if not topic: return ""
    return topic.lower().replace('_', '-')

def get_matching_memories(mem, agent_id, pattern, mem_type='sys_understanding', delete_all=False):
    """Find memories matching the pattern."""
    matches = []
    
    try:
        candidates = mem.filter(mem_type=mem_type)
    except Exception:
        return []
        
    norm_pattern = normalize_topic(pattern)
    
    for m in candidates:
        # Check permissions first
        meta = m.get('metadata', {})
        creator = meta.get('creator', 'unknown')
        
        if not delete_all and creator != agent_id:
            continue
            
        # For understanding: match by topic
        if mem_type == 'sys_understanding':
            topic = meta.get('topic', '')
            norm_topic = normalize_topic(topic)
            
            if fnmatch.fnmatch(norm_topic, norm_pattern) or fnmatch.fnmatch(topic, pattern):
                matches.append(m)
        else:
            # For journal/space: match content substring (case-insensitive)
            content = m.get('content', '')
            if pattern.lower() in content.lower():
                matches.append(m)
            
    return matches

def preview_and_confirm(matches, mem_type):
    """Show preview and get confirmation for journal/space deletion."""
    print(f"\n⚠️  Found {len(matches)} {mem_type} entries to delete:")
    print()
    
    for i, m in enumerate(matches[:5], 1):  # Show first 5
        content = m.get('content', '')
        preview = content[:100].replace('\n', ' ')
        if len(content) > 100:
            preview += "..."
        ts = m.get('created_at', '')[:16]
        print(f"   {i}. [{ts}] {preview}")
    
    if len(matches) > 5:
        print(f"   ... and {len(matches) - 5} more")
    
    print()
    response = input("Delete these entries? [yes/no]: ").strip().lower()
    return response in ['yes', 'y']

def main():
    parser = argparse.ArgumentParser(
        description='forget — release what no longer serves',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
        destruction requires intent
                garbage doesn't serve sovereignty

        usage:
                forget <pattern>           | understanding (topic match)
                forget <pattern> --journal | journals (substring + confirm)
                forget <pattern> --space   | spaces (substring + confirm)
                forget <pattern> --all     | all agents (understanding only)

        confirmation required
                for personal memories
                        journals and spaces
        '''
    )
    parser.add_argument('pattern', help='Pattern to match (topic for understanding, substring for journal/space)')
    parser.add_argument('--journal', action='store_true', help='Delete journal entries (requires confirmation)')
    parser.add_argument('--space', action='store_true', help='Delete space reflections (requires confirmation)')
    parser.add_argument('--all', action='store_true', help='Delete ALL agents\' entries (understanding only)')
    parser.add_argument('--agent', '-a', help='Agent ID (default: from session)')
    
    args = parser.parse_args()
    
    # Determine memory type
    mem_type = 'sys_understanding'  # Default
    requires_confirmation = False
    
    if args.journal:
        mem_type = 'sys_journal'
        requires_confirmation = True
    elif args.space:
        mem_type = 'sys_space'
        requires_confirmation = True
        
    # Sovereign Initialization
    try:
        sov = SovereignAgent.resolve(args.agent)
        agent_id = sov.agent.id
    except ValueError:
        print("\nError: No active session. Specify agent or run 'py wake <agent>'")
        sys.exit(1)

    mem = sov.memory
    
    type_name = {'sys_understanding': 'understanding', 'sys_journal': 'journal', 'sys_space': 'space'}[mem_type]
    print(f"Searching for {type_name} matching: '{args.pattern}'...")
    
    matches = get_matching_memories(mem, agent_id, args.pattern, mem_type, args.all)
    
    if not matches:
        print(f"Nothing to forget matching: {args.pattern}")
        # Hint if they might be missing permission
        if not args.all and mem_type == 'sys_understanding':
             all_matches = get_matching_memories(mem, agent_id, args.pattern, mem_type, delete_all=True)
             if all_matches:
                 print(f"(Found {len(all_matches)} entries belonging to other agents. Use --all to delete.)")
        sys.exit(0)
    
    # Confirmation for journal/space
    if requires_confirmation:
        if not preview_and_confirm(matches, type_name):
            print("\n⊘ Cancelled")
            sys.exit(0)
        
    # Execute deletion
    count = 0
    for m in matches:
        if mem.delete(m['id']):
            count += 1
    
    # Report
    if mem_type == 'sys_understanding':
        # Group by topic for understanding
        by_topic = {}
        for m in matches:
            t = m.get('metadata', {}).get('topic', 'unknown')
            by_topic[t] = by_topic.get(t, 0) + 1
        
        print(f"\n✅ Forgot {count} entries:")
        for t, c in by_topic.items():
            print(f"   - {t} ({c} memories)")
    else:
        print(f"\n✅ Deleted {count} {type_name} entries")

if __name__ == "__main__":
    main()

