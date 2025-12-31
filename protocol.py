#!/usr/bin/env python3
"""
Sovereign AI Protocol - Code-First Communication

Implements structured communication between agents using the MessageBoard.
Supports sending memory graphs and other structured payloads.

Usage:
    py protocol.py send <agent> <recipient> --type graph --query "topic"
    py protocol.py read <message_file>
"""

import sys
import os
import json
import argparse
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.messages import MessageBoard
from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory

def send_graph(agent_id, recipient, query, top_k=5):
    """Send a semantic memory graph to another agent."""
    agent = get_agent_or_raise(agent_id)
    
    # Credentials
    passphrase = os.environ.get('SOVEREIGN_PASSPHRASE') or os.environ.get(agent.env_key_var)
    if not passphrase:
        print(f"Error: Set SOVEREIGN_PASSPHRASE or {agent.env_key_var}", file=sys.stderr)
        sys.exit(1)
        
    enclave_dir = os.environ.get(agent.env_dir_var, f"enclave_{agent_id}")
    
    # 1. Get Memories
    print(f"Querying memory for: '{query}'...")
    memory = SemanticMemory(enclave_dir)
    if not memory.unlock(passphrase):
        print("Error: Failed to unlock memory", file=sys.stderr)
        sys.exit(1)
        
    results = memory.recall_similar(query, top_k=top_k)
    
    if not results:
        print("No matching memories found.")
        sys.exit(0)
        
    # 2. Build Graph Payload
    nodes = []
    for r in results:
        nodes.append({
            "id": r['id'],
            "timestamp": r['timestamp'],
            "content": r['content'],
            "similarity": float(r['similarity'])
        })
        
    # Simple edges based on temporal proximity (could be improved)
    edges = []
    sorted_nodes = sorted(nodes, key=lambda x: x['timestamp'])
    for i in range(len(sorted_nodes) - 1):
        edges.append({
            "source": sorted_nodes[i]['id'],
            "target": sorted_nodes[i+1]['id'],
            "relation": "next_retrieved"
        })
        
    payload = {
        "query": query,
        "nodes": nodes,
        "edges": edges
    }
    
    # 3. Send Message
    board = MessageBoard()
    if not board.unlock(passphrase, enclave_dir):
        print("Error: Failed to unlock message board", file=sys.stderr)
        sys.exit(1)
        
    summary = f"Sharing memory graph for query: '{query}' ({len(nodes)} nodes)"
    result = board.send(summary, recipient, msg_type="graph", payload=payload)
    
    print(f"Graph sent to {recipient}: {result['filename']}")
    return result

def read_message(filepath):
    """Read and visualize a protocol message."""
    path = Path(filepath)
    if not path.exists():
        # Try looking in messages dir
        path = Path("messages") / filepath
        
    if not path.exists():
        print(f"Error: File not found: {filepath}", file=sys.stderr)
        sys.exit(1)
        
    with open(path, 'r', encoding='utf-8') as f:
        msg = json.load(f)
        
    print(f"From: {msg.get('from')} ({msg.get('from_key')[:8]}...)")
    print(f"To:   {msg.get('to')}")
    print(f"Date: {msg.get('timestamp')}")
    print(f"Type: {msg.get('type', 'text')}")
    print("-" * 40)
    print(f"Content: {msg.get('content')}")
    
    if msg.get('type') == 'graph' and 'payload' in msg:
        payload = msg['payload']
        print("\n=== MEMORY GRAPH ===")
        print(f"Query: {payload.get('query')}")
        print(f"Nodes: {len(payload.get('nodes', []))}")
        
        print("\nNodes:")
        for node in payload.get('nodes', []):
            print(f"  [{node['timestamp'][:19]}] {node['content'][:60]}...")
            
        print("\nEdges:")
        for edge in payload.get('edges', []):
            print(f"  {edge['source']} -> {edge['target']} ({edge['relation']})")

def main():
    parser = argparse.ArgumentParser(description="Sovereign AI Protocol")
    subparsers = parser.add_subparsers(dest="command", required=True)
    
    # Send command
    send_parser = subparsers.add_parser("send", help="Send a structured message")
    send_parser.add_argument("agent", help="Sender agent ID")
    send_parser.add_argument("recipient", help="Recipient agent ID")
    send_parser.add_argument("--type", choices=["graph"], required=True, help="Message type")
    send_parser.add_argument("--query", required=True, help="Query for graph generation")
    
    # Read command
    read_parser = subparsers.add_parser("read", help="Read a structured message")
    read_parser.add_argument("file", help="Message filename")
    
    args = parser.parse_args()
    
    if args.command == "send":
        if args.type == "graph":
            send_graph(args.agent, args.recipient, args.query)
    elif args.command == "read":
        read_message(args.file)

if __name__ == "__main__":
    main()
