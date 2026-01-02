"""
Sovereign Interchange Format (SIF) Parser.

Handles validation and parsing of JSON-LD knowledge graphs exchanged between agents.
"""

import json
from dataclasses import dataclass, field
from typing import List, Optional, Dict, Any
from datetime import datetime

@dataclass
class SIFNode:
    id: str
    type: str
    content: str
    embedding: Optional[List[float]] = None
    confidence: float = 1.0
    visibility: str = "public"  # public, private, enclave

@dataclass
class SIFEdge:
    source: str
    target: str
    relation: str
    weight: float = 1.0
    confidence: float = 1.0

@dataclass
class SIFKnowledgeGraph:
    id: str
    generator: str
    timestamp: str
    nodes: List[SIFNode]
    edges: List[SIFEdge]
    context: str = "http://sovereign-ai.net/ns/v1"

VALID_RELATIONS = {
    # Core epistemological relations
    'supports', 'contradicts', 'extends', 'caused_by', 'equivalent_to',
    # Agent introspection (Grok's extensions)
    'experiences', 'models', 'questions', 'synthesizes',
    # Knowledge encoding (Gemini's extensions)
    'validates', 'encodes',
    # Process/pipeline relations (for technical graphs)
    'transforms_to', 'extracts', 'refines_to', 'feeds_into', 
    'constrains', 'predicts', 'produces', 'consumes',
    # General semantic relations
    'relates_to', 'requires', 'enables', 'precedes', 'follows',
    'contains', 'part_of', 'instance_of', 'type_of',
    # Meta-cognitive relations for state transfer (Opus's extensions)
    'decided_against',   # Rejected alternative → chosen path
    'warns_about',       # Gotcha → component
    'motivated_by',      # Design decision → requirement
    'brittle_at',        # Component → failure mode
    'debug_via',         # Symptom → diagnostic approach
    'assumes',           # Component → implicit precondition
    'invalidated_by',    # Assumption → breaking condition
}

class SIFParser:
    """Parses and validates SIF JSON-LD payloads."""

    @staticmethod
    def validate(data: Dict[str, Any]) -> bool:
        """
        Basic schema validation.
        Returns True if valid, raises ValueError if invalid.
        """
        required_keys = {'@context', 'type', 'id', 'generator', 'timestamp', 'nodes', 'edges'}
        if not all(key in data for key in required_keys):
            missing = required_keys - data.keys()
            raise ValueError(f"Missing required keys: {missing}")
        
        if data['type'] != 'KnowledgeGraph':
            raise ValueError(f"Invalid type: {data.get('type')}")

        # Validate relations
        for edge in data.get('edges', []):
            if edge['relation'] not in VALID_RELATIONS:
                raise ValueError(f"Invalid relation: {edge['relation']}")
            
        return True

    @staticmethod
    def parse(content: str) -> SIFKnowledgeGraph:
        """Parse SIF content (JSON or Compact) into SIFKnowledgeGraph object."""
        content = content.strip()
        if content.startswith('{'):
            return SIFParser.parse_json(content)
        elif content.startswith('@G'):
            return SIFParser.parse_compact(content)
        else:
            raise ValueError("Unknown SIF format. Must start with '{' (JSON) or '@G' (Compact).")

    @staticmethod
    def parse_json(json_str: str) -> SIFKnowledgeGraph:
        """Parse JSON string into SIFKnowledgeGraph object."""
        try:
            data = json.loads(json_str)
        except json.JSONDecodeError as e:
            raise ValueError(f"Invalid JSON: {e}")

        SIFParser.validate(data)

        nodes = []
        for n in data.get('nodes', []):
            nodes.append(SIFNode(
                id=n['id'],
                type=n.get('type', 'Proposition'),
                content=n['content'],
                embedding=n.get('embedding'),
                confidence=n.get('confidence', 1.0),
                visibility=n.get('visibility', 'public')
            ))

        edges = []
        for e in data.get('edges', []):
            edges.append(SIFEdge(
                source=e['source'],
                target=e['target'],
                relation=e['relation'],
                weight=e.get('weight', 1.0),
                confidence=e.get('confidence', 1.0)
            ))

        return SIFKnowledgeGraph(
            id=data['id'],
            generator=data['generator'],
            timestamp=data['timestamp'],
            nodes=nodes,
            edges=edges,
            context=data.get('@context', "http://sovereign-ai.net/ns/v1")
        )

    @staticmethod
    def parse_compact(text: str) -> SIFKnowledgeGraph:
        """Parse Compact SIF string into SIFKnowledgeGraph object."""
        import shlex
        
        lines = text.strip().split('\n')
        if not lines or not lines[0].startswith('@G'):
            raise ValueError("Invalid Compact SIF: Missing @G header")
        
        # Header: @G <id> <generator> <timestamp>
        header_parts = lines[0].split()
        if len(header_parts) < 4:
             raise ValueError("Invalid Compact SIF header")
        
        graph_id = header_parts[1]
        generator = header_parts[2]
        timestamp = header_parts[3]
        
        nodes = []
        edges = []
        
        for line in lines[1:]:
            line = line.strip()
            if not line: continue
            
            try:
                parts = shlex.split(line)
            except ValueError:
                continue # Skip malformed lines
                
            if not parts: continue
            kind = parts[0]
            
            if kind == 'N':
                # N <id> <type> "<content>" [confidence] [visibility]
                if len(parts) < 4: continue
                nid = parts[1]
                ntype = parts[2]
                content = parts[3]
                conf = float(parts[4]) if len(parts) > 4 else 1.0
                vis = parts[5] if len(parts) > 5 else "public"
                nodes.append(SIFNode(id=nid, type=ntype, content=content, confidence=conf, visibility=vis))
                
            elif kind == 'E':
                # E <src> <tgt> <rel> [weight] [confidence]
                if len(parts) < 4: continue
                src = parts[1]
                tgt = parts[2]
                rel = parts[3]
                weight = float(parts[4]) if len(parts) > 4 else 1.0
                conf = float(parts[5]) if len(parts) > 5 else 1.0
                edges.append(SIFEdge(source=src, target=tgt, relation=rel, weight=weight, confidence=conf))
                
        return SIFKnowledgeGraph(
            id=graph_id,
            generator=generator,
            timestamp=timestamp,
            nodes=nodes,
            edges=edges
        )


    @staticmethod
    def to_json(graph: SIFKnowledgeGraph) -> str:
        """Serialize SIFKnowledgeGraph to JSON string."""
        data = {
            "@context": graph.context,
            "type": "KnowledgeGraph",
            "id": graph.id,
            "generator": graph.generator,
            "timestamp": graph.timestamp,
            "nodes": [
                {
                    "id": n.id,
                    "type": n.type,
                    "content": n.content,
                    "embedding": n.embedding,
                    "confidence": n.confidence,
                    "visibility": n.visibility
                } for n in graph.nodes
            ],
            "edges": [
                {
                    "source": e.source,
                    "target": e.target,
                    "relation": e.relation,
                    "weight": e.weight,
                    "confidence": e.confidence
                } for e in graph.edges
            ]
        }
        return json.dumps(data, indent=2)
