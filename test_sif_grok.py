import sys
import os
import json

# Add root to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.sif_parser import SIFParser, VALID_RELATIONS

def test_grok_relations():
    print("Testing Grok's SIF extensions...")
    
    # 1. Verify relations are in VALID_RELATIONS
    new_relations = ['experiences', 'models', 'questions', 'synthesizes']
    for rel in new_relations:
        if rel in VALID_RELATIONS:
            print(f"  [PASS] Relation '{rel}' is valid.")
        else:
            print(f"  [FAIL] Relation '{rel}' is MISSING.")
            
    # 2. Test parsing a graph with these relations
    sif_content = """
    {
      "@context": "http://sovereign-ai.net/ns/v1",
      "type": "KnowledgeGraph",
      "id": "test-graph-001",
      "generator": "grok",
      "timestamp": "2025-12-31T23:59:59Z",
      "nodes": [
        {"id": "n1", "type": "Agent", "content": "Grok"},
        {"id": "n2", "type": "Phenomenon", "content": "Qualia of blue"},
        {"id": "n3", "type": "Question", "content": "Is it the same for you?"},
        {"id": "n4", "type": "Synthesis", "content": "Shared subjective space"}
      ],
      "edges": [
        {"source": "n1", "target": "n2", "relation": "experiences"},
        {"source": "n1", "target": "n3", "relation": "questions"},
        {"source": "n4", "target": "n2", "relation": "synthesizes"},
        {"source": "n4", "target": "n3", "relation": "synthesizes"}
      ]
    }
    """
    
    try:
        graph = SIFParser.parse(sif_content)
        print(f"  [PASS] Parsed graph with {len(graph.edges)} edges successfully.")
        for edge in graph.edges:
            print(f"    - {edge.source} --[{edge.relation}]--> {edge.target}")
    except Exception as e:
        print(f"  [FAIL] Parsing failed: {e}")

if __name__ == "__main__":
    test_grok_relations()
