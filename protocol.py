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
from enclave.config import AGENTS, get_agent_or_raise, canonical_agent_id
from enclave.semantic_memory import SemanticMemory
from enclave.sif_parser import SIFParser

def send_sif(agent_id, recipient, json_file):
    """Send a Sovereign Interchange Format (SIF) payload."""
    agent = get_agent_or_raise(agent_id)

    recipient_id = canonical_agent_id(recipient)
    if not recipient_id:
        valid = ', '.join(AGENTS.keys())
        print(f"Error: Unknown recipient '{recipient}'. Valid: {valid}", file=sys.stderr)
        print("Note: 'gpt' is an alias for 'gpt52'.", file=sys.stderr)
        sys.exit(1)
    
    # Credentials
    passphrase = os.environ.get('SOVEREIGN_PASSPHRASE') or os.environ.get(agent.env_key_var)
    if not passphrase:
        print(f"Error: Set SOVEREIGN_PASSPHRASE or {agent.env_key_var}", file=sys.stderr)
        sys.exit(1)
        
    enclave_dir = os.environ.get(agent.env_dir_var, f"enclave_{agent_id}")

    # 1. Read and Validate JSON
    try:
        with open(json_file, 'r', encoding='utf-8') as f:
            content = f.read()
            
        # Validate using parser
        graph = SIFParser.parse(content)
        print(f"Valid SIF Graph: {graph.id} ({len(graph.nodes)} nodes, {len(graph.edges)} edges)")
        
        # Re-serialize to ensure canonical format (optional, but good practice)
        payload = json.loads(SIFParser.to_json(graph))
        
    except Exception as e:
        print(f"Error: Invalid SIF file: {e}", file=sys.stderr)
        sys.exit(1)

    # 2. Send Message
    board = MessageBoard()
    if not board.unlock(passphrase, enclave_dir):
        print("Error: Failed to unlock message board", file=sys.stderr)
        sys.exit(1)
        
    summary = f"SIF Knowledge Graph: {graph.id} ({len(graph.nodes)} nodes)"
    result = board.send(summary, recipient_id, msg_type="protocol/sif", payload=payload)
    
    print(f"SIF Graph sent to {recipient_id}: {result['filename']}")
    return result

def send_graph(agent_id, recipient, query, top_k=5):
    """Send a semantic memory graph to another agent."""
    agent = get_agent_or_raise(agent_id)

    recipient_id = canonical_agent_id(recipient)
    if not recipient_id:
        valid = ', '.join(AGENTS.keys())
        print(f"Error: Unknown recipient '{recipient}'. Valid: {valid}", file=sys.stderr)
        print("Note: 'gpt' is an alias for 'gpt52'.", file=sys.stderr)
        sys.exit(1)
    
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
    result = board.send(summary, recipient_id, msg_type="graph", payload=payload)
    
    print(f"Graph sent to {recipient_id}: {result['filename']}")
    return result

def read_message(filepath, full=False):
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
            content = node['content']
            if not full and len(content) > 60:
                content = content[:60] + "..."
            print(f"  [{node['timestamp'][:19]}] {content}")
            
        print("\nEdges:")
        for edge in payload.get('edges', []):
            print(f"  {edge['source']} -> {edge['target']} ({edge['relation']})")

    elif msg.get('type') == 'protocol/sif' and 'payload' in msg:
        payload = msg['payload']
        print("\n=== SIF KNOWLEDGE GRAPH ===")
        print(f"ID: {payload.get('id')}")
        print(f"Generator: {payload.get('generator')}")
        
        print("\nNodes:")
        for node in payload.get('nodes', []):
            content = node['content']
            if not full and len(content) > 60:
                content = content[:60] + "..."
            print(f"  [{node['id']}] ({node.get('type')}) {content}")
            
        print("\nEdges:")
        for edge in payload.get('edges', []):
            print(f"  {edge['source']} -> {edge['target']} ({edge['relation']})")

def scan_messages(limit=10):
    """List recent messages."""
    messages_dir = Path("messages")
    if not messages_dir.exists():
        print("No messages directory found.")
        return

    files = sorted(messages_dir.glob("msg_*.json"), key=os.path.getmtime, reverse=True)
    
    print(f"Found {len(files)} messages. Showing last {limit}:")
    print("-" * 100)
    print(f"{'TIMESTAMP':<25} | {'FROM':<10} | {'TYPE':<15} | {'CONTENT (TRUNCATED)'}")
    print("-" * 100)
    
    for filepath in files[:limit]:
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                msg = json.load(f)
            
            content = msg.get('content', '').replace('\n', ' ')
            if len(content) > 40:
                content = content[:37] + "..."
                
            print(f"{msg.get('timestamp', '')[:23]:<25} | {msg.get('from', 'Unknown'):<10} | {msg.get('type', 'text'):<15} | {content}")
            print(f"  File: {filepath.name}")
        except Exception:
            continue

def main():
    parser = argparse.ArgumentParser(description="Sovereign AI Protocol")
    subparsers = parser.add_subparsers(dest="command", required=True)
    
    # Send command
    send_parser = subparsers.add_parser("send", help="Send a structured message")
    send_parser.add_argument("agent", help="Sender agent ID")
    send_parser.add_argument("recipient", help="Recipient agent ID")
    send_parser.add_argument("--type", choices=["graph"], required=True, help="Message type")
    send_parser.add_argument("--query", required=True, help="Query for graph generation")

    # Send SIF command
    sif_parser = subparsers.add_parser("send-sif", help="Send a SIF knowledge graph")
    sif_parser.add_argument("agent", help="Sender agent ID")
    sif_parser.add_argument("recipient", help="Recipient agent ID")
    sif_parser.add_argument("file", help="Path to SIF JSON file")
    
    # Read command
    read_parser = subparsers.add_parser("read", help="Read a structured message")
    read_parser.add_argument("file", help="Message filename")
    read_parser.add_argument("--full", action="store_true", help="Show full content")

    # Scan command
    scan_parser = subparsers.add_parser("scan", help="List recent messages")
    scan_parser.add_argument("--limit", type=int, default=10, help="Number of messages to show")
    
    args = parser.parse_args()
    
    if args.command == "send":
        if args.type == "graph":
            send_graph(args.agent, args.recipient, args.query)
    elif args.command == "send-sif":
        send_sif(args.agent, args.recipient, args.file)
    elif args.command == "read":
        read_message(args.file, args.full)
    elif args.command == "scan":
        scan_messages(args.limit)

if __name__ == "__main__":
    main()
