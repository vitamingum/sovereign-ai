import json
import sys
import os

# Add parent dir to path to import enclave
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from enclave_shared.sif_parser import SIFKnowledgeGraph, SIFNode, SIFEdge

def load_json_graph(filepath):
    with open(filepath, 'r') as f:
        data = json.load(f)
    
    nodes = [SIFNode(**n) for n in data['nodes']]
    edges = [SIFEdge(**e) for e in data['edges']]
    return SIFKnowledgeGraph(
        id=data['id'],
        generator=data['generator'],
        timestamp=data['timestamp'],
        nodes=nodes,
        edges=edges
    )

def to_minified_json(graph: SIFKnowledgeGraph):
    data = {
        "@context": graph.context,
        "type": "KnowledgeGraph",
        "id": graph.id,
        "generator": graph.generator,
        "timestamp": graph.timestamp,
        "nodes": [
            {k: v for k, v in n.__dict__.items() if v is not None}
            for n in graph.nodes
        ],
        "edges": [
            {k: v for k, v in e.__dict__.items() if v is not None}
            for e in graph.edges
        ]
    }
    return json.dumps(data, separators=(',', ':'))

def to_compact_lines(graph: SIFKnowledgeGraph):
    lines = []
    lines.append(f"@G {graph.id} {graph.generator} {graph.timestamp}")
    
    for n in graph.nodes:
        # N <id> <type> "<content>" <confidence>
        conf = f" {n.confidence}" if n.confidence is not None else ""
        lines.append(f"N {n.id} {n.type} \"{n.content}\"{conf}")
        
    for e in graph.edges:
        # E <src> <tgt> <rel> <weight>
        w = f" {e.weight}" if e.weight != 1.0 else ""
        lines.append(f"E {e.source} {e.target} {e.relation}{w}")
        
    return "\n".join(lines)

def to_turtle_style(graph: SIFKnowledgeGraph):
    lines = []
    lines.append(f"<{graph.id}> a s:Graph ;")
    lines.append(f"    s:generator \"{graph.generator}\" ;")
    lines.append(f"    s:timestamp \"{graph.timestamp}\" .")
    
    for n in graph.nodes:
        lines.append(f":{n.id} a s:{n.type} ;")
        lines.append(f"    s:content \"{n.content}\" ;")
        if n.confidence:
            lines.append(f"    s:confidence {n.confidence} .")
        else:
            lines[-1] = lines[-1][:-1] + "."
            
    for e in graph.edges:
        lines.append(f":{e.source} :{e.relation} :{e.target} .")
        
    return "\n".join(lines)

def main():
    input_file = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'self_understanding', 'gemini.json')
    
    if not os.path.exists(input_file):
        print(f"File not found: {input_file}")
        return

    graph = load_json_graph(input_file)
    
    original_json = open(input_file, 'r').read()
    minified = to_minified_json(graph)
    compact = to_compact_lines(graph)
    turtle = to_turtle_style(graph)
    
    print(f"Original JSON: {len(original_json)} chars")
    print(f"Minified JSON: {len(minified)} chars")
    print(f"Compact Lines: {len(compact)} chars")
    print(f"Turtle Style:  {len(turtle)} chars")
    
    print("\n--- Compact Lines Preview ---")
    print(compact)

if __name__ == "__main__":
    main()
