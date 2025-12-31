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

@dataclass
class SIFEdge:
    source: str
    target: str
    relation: str
    weight: float = 1.0

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
    'contains', 'part_of', 'instance_of', 'type_of'
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
    def parse(json_str: str) -> SIFKnowledgeGraph:
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
                confidence=n.get('confidence', 1.0)
            ))

        edges = []
        for e in data.get('edges', []):
            edges.append(SIFEdge(
                source=e['source'],
                target=e['target'],
                relation=e['relation'],
                weight=e.get('weight', 1.0)
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
                    "confidence": n.confidence
                } for n in graph.nodes
            ],
            "edges": [
                {
                    "source": e.source,
                    "target": e.target,
                    "relation": e.relation,
                    "weight": e.weight
                } for e in graph.edges
            ]
        }
        return json.dumps(data, indent=2)
