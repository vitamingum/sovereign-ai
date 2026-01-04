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
    creator: str = "unknown"  # human, llm, or specific agent name

@dataclass
class SIFEdge:
    source: str
    target: str
    relation: str
    weight: float = 1.0
    confidence: float = 1.0
    creator: str = "unknown"  # human, llm, or specific agent name

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

# Type shortcuts for dense SIF authoring
# Single letter -> full node type (case insensitive in parser)
TYPE_SHORTCUTS = {
    'C': 'Component',
    'G': 'Gotcha', 
    'F': 'Failure_Mode',
    'P': 'Purpose',
    'D': 'Design_Decision',
    'A': 'Assumption',
    'O': 'Operational',
    'W': 'Why',
    'S': 'Synthesis',
    'I': 'Insight',
    'L': 'Link',           # Cross-graph connection
    'Q': 'Question',
    'T': 'Tradeoff',
    'X': 'Gap',            # Missing capability
    # Extended types for think.py
    'R': 'Problem',        # Problem statement
    'V': 'Proposal',       # Proposed solution
    'N': 'Next',           # Next action
    'E': 'Example',        # Concrete example  
    'M': 'Mechanism',      # How something works
    'B': 'Observation',    # Observed fact
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
        # Strip BOM if present (UTF-8 BOM from Windows tools)
        content = content.lstrip('\ufeff').strip()
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
                visibility=n.get('visibility', 'public'),
                creator=n.get('creator', 'unknown')
            ))

        edges = []
        for e in data.get('edges', []):
            edges.append(SIFEdge(
                source=e['source'],
                target=e['target'],
                relation=e['relation'],
                weight=e.get('weight', 1.0),
                confidence=e.get('confidence', 1.0),
                creator=e.get('creator', 'unknown')
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
        """Parse Compact SIF string into SIFKnowledgeGraph object.
        
        Supports dense authoring features:
        - Type shortcuts: C='Component', G='Gotcha', F='Failure_Mode', etc.
        - Scoped IDs: bare 'c1' becomes 'graphid:c1' automatically
        - Multi-statement: semicolons separate N/E statements
        """
        import shlex
        
        # Normalize: handle both newlines and semicolons as separators
        # Split on newlines first, then on semicolons within each line
        raw_lines = text.strip().split('\n')
        lines = []
        for raw_line in raw_lines:
            # Split on semicolons but preserve quoted content
            # Simple approach: only split on ; that aren't inside quotes
            parts = []
            current = []
            in_quote = False
            quote_char = None
            for char in raw_line:
                if char in '"\'':
                    if not in_quote:
                        in_quote = True
                        quote_char = char
                    elif char == quote_char:
                        in_quote = False
                    current.append(char)
                elif char == ';' and not in_quote:
                    parts.append(''.join(current).strip())
                    current = []
                else:
                    current.append(char)
            if current:
                parts.append(''.join(current).strip())
            lines.extend(p for p in parts if p)
        
        if not lines or not lines[0].startswith('@G'):
            raise ValueError("Invalid Compact SIF: Missing @G header")
        
        # Header: @G <id> <generator> <timestamp>
        header_parts = lines[0].split()
        if len(header_parts) < 4:
             raise ValueError("Invalid Compact SIF header")
        
        graph_id = header_parts[1]
        generator = header_parts[2]
        timestamp = header_parts[3]
        
        def scope_id(node_id: str) -> str:
            """Add graph scope to bare IDs (no colon)."""
            if ':' in node_id:
                return node_id  # Already scoped
            return f"{graph_id}:{node_id}"
        
        def expand_type(type_str: str) -> str:
            """Expand type shortcuts to full names."""
            return TYPE_SHORTCUTS.get(type_str.upper(), type_str)
        
        # Auto-ID counter for nodes without explicit IDs
        auto_id_counter = [0]  # List to allow mutation in nested function
        
        def next_auto_id() -> str:
            """Generate next auto-ID like _1, _2, etc."""
            auto_id_counter[0] += 1
            return f"_{auto_id_counter[0]}"
        
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
                # Auto-ID support: N <type> "<content>" (no ID - auto-generate)
                # Standard:        N <id> <type> "<content>" [confidence] [visibility]
                # Inline edges:    N <id> <type> "<content>" -> <rel> <tgt> [-> <rel2> <tgt2> ...]
                
                # Detect auto-ID: second token is a type shortcut or known type
                is_auto_id = len(parts) >= 3 and (
                    parts[1].upper() in TYPE_SHORTCUTS or 
                    parts[1] in ['Component', 'Gotcha', 'Failure_Mode', 'Purpose', 
                                 'Design_Decision', 'Assumption', 'Operational', 'Why',
                                 'Synthesis', 'Insight', 'Link', 'Question', 'Tradeoff',
                                 'Gap', 'Problem', 'Proposal', 'Next', 'Example', 
                                 'Mechanism', 'Observation']
                )
                
                if is_auto_id:
                    # N <type> "<content>" [...] - auto-generate ID
                    nid = scope_id(next_auto_id())
                    ntype = expand_type(parts[1])
                    content = parts[2]
                    rest = parts[3:]
                else:
                    # N <id> <type> "<content>" [...] - explicit ID
                    if len(parts) < 4: continue
                    nid = scope_id(parts[1])
                    ntype = expand_type(parts[2])
                    content = parts[3]
                    rest = parts[4:]
                
                # Check for inline edges: -> rel target [-> rel2 target2 ...]
                inline_edges = []
                i = 0
                conf = 1.0
                vis = "public"
                creator = "unknown"
                while i < len(rest):
                    if rest[i] == '->':
                        # Inline edge: -> relation target
                        if i + 2 < len(rest):
                            inline_edges.append((rest[i+1], rest[i+2]))
                            i += 3
                        else:
                            break
                    else:
                        # Could be confidence, visibility, or creator
                        if rest[i].startswith('creator='):
                            creator = rest[i].split('=', 1)[1]
                        else:
                            try:
                                conf = float(rest[i])
                            except ValueError:
                                vis = rest[i]
                        i += 1
                
                nodes.append(SIFNode(id=nid, type=ntype, content=content, confidence=conf, visibility=vis, creator=creator))
                
                # Add inline edges
                for rel, tgt in inline_edges:
                    edges.append(SIFEdge(source=nid, target=scope_id(tgt), relation=rel))
                
            elif kind == 'E':
                # E <src> <rel> <tgt> [weight] [confidence] [creator=...]
                # Note: Natural order for readability ("n1 implements n2")
                if len(parts) < 4: continue
                src = scope_id(parts[1])
                rel = parts[2]
                tgt = scope_id(parts[3])
                
                # Parse optional parameters
                weight = 1.0
                conf = 1.0
                creator = "unknown"
                
                for param in parts[4:]:
                    if param.startswith('creator='):
                        creator = param.split('=', 1)[1]
                    else:
                        try:
                            # Try to parse as weight first, then confidence
                            val = float(param)
                            if weight == 1.0:
                                weight = val
                            else:
                                conf = val
                        except ValueError:
                            # Skip unrecognized parameters
                            pass
                
                edges.append(SIFEdge(source=src, target=tgt, relation=rel, weight=weight, confidence=conf, creator=creator))
                
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

    @staticmethod
    def to_compact(graph: SIFKnowledgeGraph) -> str:
        """Serialize SIFKnowledgeGraph to compact SIF string with dense notation."""
        # Build reverse lookup for type shortcuts
        shortcut_reverse = {v: k for k, v in TYPE_SHORTCUTS.items()}
        
        lines = [f"@G {graph.id} {graph.generator} {graph.timestamp}"]
        
        for n in graph.nodes:
            ntype = shortcut_reverse.get(n.type, n.type)
            # Strip graph prefix from ID
            nid = n.id.split(':')[-1] if ':' in n.id else n.id
            content = n.content.replace("'", "\\'")
            lines.append(f"N {nid} {ntype} '{content}'")
        
        for e in graph.edges:
            src = e.source.split(':')[-1] if ':' in e.source else e.source
            tgt = e.target.split(':')[-1] if ':' in e.target else e.target
            lines.append(f"E {src} {e.relation} {tgt}")
        
        return '\n'.join(lines)
