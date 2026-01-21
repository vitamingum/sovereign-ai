#!/usr/bin/env python3
"""
accord.py - consensus > vote  distributed agreement

    source: data/accord.flow
    context: data/sovereign.flow
    compiler: gemini (manual)
    date: 2026-01-14

intent
  deliberate on proposals
  reach quorum (ratification)
  block execution if pending

flow
  propose(topic, @draft)
  -> deliberate(signatures, amendments)
  -> sign(hash)
  -> quorum?
     | yes -> ratify -> shared_memory
     | no  -> wait
"""

import sys
import argparse
import time
from pathlib import Path

# Context: sovereign.flow -> environment.libs
sys.path.insert(0, str(Path(__file__).parent.parent))

from lib_enclave.sovereign_agent import SovereignAgent
from lib_enclave import consensus
from lib_enclave.interaction import interactive_capture

def cmd_status(me: SovereignAgent):
    # sovereign.flow: scan() equivalent for accord
    agent_id = me.agent.name if me else None
    
    proposals = consensus.get_pending_proposals(agent_id)
    
    if not proposals:
        print("✅ No pending proposals")
        return
        
    print(f"📜 Pending proposals:\n")
    for p in proposals:
        marker = "⏳" if p.get('needs_me') else "✓"
        print(f"  {marker} {p['topic']} ({p['signatures']}/{p['quorum']} signatures)")
        if p['signers']:
            print(f"      Signed by: {', '.join(p['signers'])}")
        if p.get('needs_me'):
            print(f"      → Run: py accord.py deliberate {agent_id} {p['topic']}")
    print()

def cmd_deliberate(me: SovereignAgent, topic: str):
    path = consensus.proposal_path(topic)
    proposal = consensus.parse_proposal(path)
    
    if not proposal:
        print(f"❌ Proposal '{topic}' not found")
        sys.exit(1)
        
    final_body = consensus.apply_amendments(proposal.body, proposal.deliberations)
    final_hash = consensus.compute_body_hash(final_body)
    
    print(f"═══ Proposal: {topic} ═══")
    print(f"Status: {proposal.status}")
    print(f"Quorum: {proposal.quorum}")
    print(f"Hash:   {final_hash}")
    print("\nBody:\n")
    print(proposal.body)
    print("\nDeliberation:\n")
    for agent, op, args in proposal.deliberations:
        print(f"  {agent}: {op} {args}")
        
    valid_count, signers = consensus.count_valid_signatures(proposal)
    print(f"\nSignatures: {valid_count}/{proposal.quorum} ({', '.join(signers)})")
    
    if me:
        print(f"\nAction: py accord.py sign {me.agent.name} {topic}")

def cmd_sign(me: SovereignAgent, topic: str):
    if not me:
        print("Auth required to sign")
        sys.exit(1)
        
    # Verify Identity exists (Auth-Once)
    _ = me.identity

    path = consensus.proposal_path(topic)
    proposal = consensus.parse_proposal(path)
    if not proposal:
        sys.exit(1)
        
    final_body = consensus.apply_amendments(proposal.body, proposal.deliberations)
    final_hash = consensus.compute_body_hash(final_body)
    
    proposal.deliberations.append((me.agent.name, 'SIGN', final_hash))
    consensus.write_proposal(proposal, path)
    
    print(f"✅ {me.agent.name} signed {topic} ({final_hash})")
    
    valid_count, _ = consensus.count_valid_signatures(proposal)
    if valid_count >= proposal.quorum:
        print(f"🎉 Quorum reached! Run: py accord.py ratify {topic}")

def main():
    parser = argparse.ArgumentParser(description="consensus > vote  distributed agreement")
    subparsers = parser.add_subparsers(dest="command")
    
    # Status
    parser_status = subparsers.add_parser("status")
    parser_status.add_argument("agent", nargs="?", help="filter for agent")
    
    # Propose
    parser_propose = subparsers.add_parser("propose")
    parser_propose.add_argument("topic")
    parser_propose.add_argument("content")
    
    # Deliberate
    parser_delib = subparsers.add_parser("deliberate")
    parser_delib.add_argument("agent")
    parser_delib.add_argument("topic")
    
    # Sign (and other actions)
    parser_sign = subparsers.add_parser("sign")
    parser_sign.add_argument("agent")
    parser_sign.add_argument("topic")
    
    # Ratify
    parser_ratify = subparsers.add_parser("ratify")
    parser_ratify.add_argument("topic")
    
    args = parser.parse_args()
    
    # Auth Resolution
    # Some commands allow explicit agent arg override, but we try default first
    agent_id_arg = getattr(args, 'agent', None)
    
    try:
        # If specific agent requested in CLI, use it (SovereignAgent.resolve logic)
        # If not, try session.
        me = SovereignAgent.resolve(agent_id_arg)
    except Exception:
        me = None

    if args.command == "status":
        if not me and agent_id_arg:
             # Just viewing status for another agent without being them?
             # But cmd_status logic uses 'needs_me' based on 'me'
             pass
        cmd_status(me)
        
    elif args.command == "deliberate":
        cmd_deliberate(me, args.topic)
        
    elif args.command == "sign":
        cmd_sign(me, args.topic)
        
    elif args.command == "propose":
        # Handle content loading
        if args.content.startswith("@"):
            content = Path(args.content[1:]).read_text(encoding="utf-8")
        elif args.content == "-":
            if sys.stdin.isatty():
                content = interactive_capture()
            else:
                content = sys.stdin.read()
        else:
            content = args.content
            
        try:
            path = consensus.create_proposal(args.topic, content, proposer=me.agent.name if me else "user")
            print(f"✅ Proposal created: {path}")
        except FileExistsError as e:
            print(f"Error: {e}")
            
    elif args.command == "ratify":
        # Ratification logic (simplified port)
        path = consensus.proposal_path(args.topic)
        proposal = consensus.parse_proposal(path)
        if not proposal:
            print("Not found")
            sys.exit(1)
            
        valid, _ = consensus.count_valid_signatures(proposal)
        if valid >= proposal.quorum:
             # Save to consensus flow
            consensus.ensure_dirs()
            consensus_path = consensus.CONSENSUS_DIR / f"{args.topic}.flow"
            
            final_body = consensus.apply_amendments(proposal.body, proposal.deliberations)
            consensus_path.write_text(final_body, encoding='utf-8')
            
            proposal.status = 'ratified'
            consensus.write_proposal(proposal, path)
            print(f"🎉 Ratified: {args.topic}")
        else:
            print("Quorum not reached")
            
    else:
        # Verb Excellence: No args -> Status
        try:
             cmd_status(me)
        except Exception:
             parser.print_help()

if __name__ == "__main__":
    main()

