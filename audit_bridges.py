#!/usr/bin/env python3
"""
Audit and clean up bridges based on understanding depth.

Rules:
- If EITHER topic has 0 understanding, delete the bridge (shallow link)
- Keep bridges with evaluator="opus-4.5-deep" (human-verified)
- Keep bridges where BOTH topics have understanding

Use --conservative to only delete when BOTH topics have 0 understanding.
"""
import os
import sys
from collections import defaultdict

from dotenv import load_dotenv
load_dotenv()

from enclave.semantic_memory import SemanticMemory


def get_understanding_counts(sm):
    """Count understanding memories per topic."""
    understanding_tags = (
        sm.list_by_tag('understanding') + 
        sm.list_by_tag('gotcha') + 
        sm.list_by_tag('failure_mode') + 
        sm.list_by_tag('assumption')
    )
    
    counts = defaultdict(int)
    for u in understanding_tags:
        for tag in u.get('tags', []):
            # Extract topic from tags like "crypto-understanding", "kdf-understanding"
            if '-understanding' in tag:
                topic = tag.replace('-understanding', '')
                counts[topic] += 1
            elif tag.startswith('topic:'):
                counts[tag.replace('topic:', '')] += 1
    
    return counts


def audit_bridges(sm, dry_run=True, conservative=False):
    """Audit bridges and identify garbage.
    
    Args:
        conservative: If True, only delete when BOTH topics have 0 understanding.
                     If False (default), delete when EITHER topic has 0 understanding.
    """
    understanding = get_understanding_counts(sm)
    bridges = sm.list_by_tag('bridge')
    
    # Group bridges by topic pair
    bridge_groups = defaultdict(list)
    for b in bridges:
        meta = b.get('metadata', {})
        bridged = tuple(sorted(meta.get('bridged_topics', [])))
        if len(bridged) == 2:
            bridge_groups[bridged].append(b)
    
    to_delete = []
    to_keep = []
    to_review = []
    
    for (t1, t2), bridge_list in bridge_groups.items():
        u1 = understanding.get(t1, 0)
        u2 = understanding.get(t2, 0)
        
        # Check if any bridge in this group is from deep evaluation
        has_deep = any(
            b.get('metadata', {}).get('evaluator') == 'opus-4.5-deep' 
            for b in bridge_list
        )
        
        score = bridge_list[0].get('metadata', {}).get('relevancy_score', 0)
        evaluator = bridge_list[0].get('metadata', {}).get('evaluator', 'unknown')
        
        if has_deep:
            to_keep.append({
                'pair': (t1, t2),
                'understanding': (u1, u2),
                'score': score,
                'reason': 'deep evaluation'
            })
        elif u1 == 0 and u2 == 0:
            # Both have 0 understanding - always delete
            to_delete.extend(bridge_list)
            print(f"DELETE: {t1} <-> {t2} ({score}) - neither topic has understanding")
        elif u1 == 0 or u2 == 0:
            # One side has 0 understanding
            weak = t1 if u1 == 0 else t2
            if conservative:
                # Conservative mode: review these
                to_review.append({
                    'pair': (t1, t2),
                    'understanding': (u1, u2),
                    'score': score,
                    'reason': f'{weak} has no understanding'
                })
            else:
                # Aggressive mode: delete these too
                to_delete.extend(bridge_list)
                print(f"DELETE: {t1} <-> {t2} ({score}) - {weak} has no understanding")
        else:
            to_keep.append({
                'pair': (t1, t2),
                'understanding': (u1, u2),
                'score': score,
                'reason': 'both topics understood'
            })
    
    print(f"\n=== SUMMARY ===")
    print(f"To delete: {len(to_delete)} bridge memories ({len(set(tuple(sorted(b.get('metadata',{}).get('bridged_topics',[]))) for b in to_delete))} pairs)")
    print(f"To review: {len(to_review)} pairs")
    print(f"To keep: {len(to_keep)} pairs")
    
    if to_review:
        print(f"\n=== REVIEW NEEDED ===")
        for r in to_review[:10]:
            print(f"  {r['pair'][0]} <-> {r['pair'][1]} ({r['score']}) - {r['reason']}")
    
    if not dry_run and to_delete:
        print(f"\n=== DELETING {len(to_delete)} MEMORIES ===")
        ids_to_delete = set(b.get('id') for b in to_delete if b.get('id'))
        deleted = sm.delete_by_ids(ids_to_delete)
        print(f"Deleted {deleted} memories")
    
    return to_delete, to_review, to_keep


def main():
    passphrase = os.environ.get("ENCLAVE_OPUS_KEY")
    if not passphrase:
        print("Error: ENCLAVE_OPUS_KEY not set")
        sys.exit(1)
    
    sm = SemanticMemory("enclave_opus")
    sm.unlock(passphrase)
    
    dry_run = "--delete" not in sys.argv
    conservative = "--conservative" in sys.argv
    
    if dry_run:
        print("DRY RUN - add --delete to actually remove bridges")
        if conservative:
            print("CONSERVATIVE MODE - only delete when BOTH topics have 0 understanding")
        else:
            print("AGGRESSIVE MODE - delete when EITHER topic has 0 understanding")
        print()
    
    to_delete, to_review, to_keep = audit_bridges(sm, dry_run, conservative)


if __name__ == "__main__":
    main()
