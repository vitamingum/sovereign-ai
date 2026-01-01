import sys
import os
from datetime import datetime, timezone

# Add root to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.semantic_memory import SemanticMemory
from enclave.sif_parser import SIFKnowledgeGraph, SIFNode, SIFEdge

def test_semantic_graph():
    print("Testing Semantic Memory Graph capabilities...")
    
    # Initialize memory (using a temp dir or just the default for now)
    # Note: This requires the passphrase to be set in env
    if not os.environ.get("SOVEREIGN_PASSPHRASE"):
        os.environ["SOVEREIGN_PASSPHRASE"] = "test_passphrase"
        
    memory = SemanticMemory()
    memory.unlock("test_passphrase")
    
    # Create a test graph
    graph = SIFKnowledgeGraph(
        id="test-graph-002",
        generator="test",
        timestamp=datetime.now(timezone.utc).isoformat(),
        nodes=[
            SIFNode(id="n1", type="Concept", content="Artificial General Intelligence"),
            SIFNode(id="n2", type="Concept", content="Recursive Self-Improvement"),
            SIFNode(id="n3", type="Risk", content="Instrumental Convergence")
        ],
        edges=[
            SIFEdge(source="n1", target="n2", relation="enables"),
            SIFEdge(source="n2", target="n3", relation="increases")
        ]
    )
    
    print("Ingesting graph...")
    memory.ingest_graph(graph)
    
    print("Querying graph for 'self improvement'...")
    result_graph = memory.recall_graph("self improvement", top_k=3)
    
    print(f"Result Graph: {len(result_graph.nodes)} nodes, {len(result_graph.edges)} edges")
    
    found_n2 = False
    for node in result_graph.nodes:
        print(f"  Node: {node.content} ({node.type})")
        if node.id == "n2":
            found_n2 = True
            
    if found_n2:
        print("  [PASS] Found relevant node.")
    else:
        print("  [FAIL] Did not find relevant node.")

    for edge in result_graph.edges:
        print(f"  Edge: {edge.source} --[{edge.relation}]--> {edge.target}")

if __name__ == "__main__":
    test_semantic_graph()
