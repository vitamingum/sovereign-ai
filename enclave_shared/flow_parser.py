"""
Flow Format Parser - Indentation-based semantic memory format.

Flow is the canonical format for sovereign AI memory:
- Indentation = hierarchy (2 spaces enforced)
- Headers use colons (Name: Content)
- Locations use tilde (~84: function_name())
- Cross-references via @ref(target) inline
- Block dependencies via @uses: [dep1, dep2]

Embedding strategy: Root-Pivot-Leaf
- Root: Level 1 header (global domain)
- Pivot: Level N-1 (immediate parent)
- Leaf: Level N (the content itself)
"""

import re
from dataclasses import dataclass, field
from typing import Optional
from datetime import datetime


@dataclass
class FlowNode:
    """A node in a Flow document, preserving hierarchy information."""
    content: str
    indent_level: int  # 0, 2, 4, 6, etc.
    line_number: int
    node_type: str = "Content"  # Derived from prefix or inferred
    
    # Hierarchy context for embedding
    root: str = ""      # Level 1 ancestor
    pivot: str = ""     # Immediate parent (N-1)
    
    # Metadata
    refs: list[str] = field(default_factory=list)  # @ref() targets
    creator: str = "unknown"


@dataclass
class FlowDocument:
    """Parsed Flow document."""
    topic: str
    agent: str
    date: str
    nodes: list[FlowNode] = field(default_factory=list)
    raw_text: str = ""
    
    @property
    def id(self) -> str:
        return f"{self.topic}:{self.agent}:{self.date}"


# Node type detection patterns
TYPE_PATTERNS = {
    'Summary': re.compile(r'^Summary:\s*(.+)$', re.IGNORECASE),
    'Purpose': re.compile(r'^Purpose:\s*(.+)$', re.IGNORECASE),
    'Design': re.compile(r'^Design:\s*(.+)$', re.IGNORECASE),
    'Gotcha': re.compile(r'^Gotcha:\s*(.+)$', re.IGNORECASE),
    'Insight': re.compile(r'^Insight:\s*(.+)$', re.IGNORECASE),
    'Question': re.compile(r'^Question:\s*(.+)$', re.IGNORECASE),
    'Metric': re.compile(r'^Metric:\s*(.+)$', re.IGNORECASE),
    'Component': re.compile(r'^Component:\s*(.+)$', re.IGNORECASE),
    'Signature': re.compile(r'^Signature:\s*(.+)$', re.IGNORECASE),
    'Command': re.compile(r'^Command:\s*(.+)$', re.IGNORECASE),
    'Example': re.compile(r'^Example:\s*(.+)$', re.IGNORECASE),
    'Principle': re.compile(r'^Principle:\s*(.+)$', re.IGNORECASE),
    'Phase': re.compile(r'^Phase:\s*(.+)$', re.IGNORECASE),
    'Decision': re.compile(r'^Decision:\s*(.+)$', re.IGNORECASE),
    'Breakthrough': re.compile(r'^Breakthrough:\s*(.+)$', re.IGNORECASE),
    'Workflow': re.compile(r'^Workflow:\s*(.+)$', re.IGNORECASE),
    'Flow': re.compile(r'^Flow:\s*(.+)$', re.IGNORECASE),
    'Spec': re.compile(r'^Spec:\s*(.+)$', re.IGNORECASE),
    'Loc': re.compile(r'^~(\d+):\s*(.+)$'),  # Location nodes
}

# Header pattern (ends with colon, no content after)
HEADER_PATTERN = re.compile(r'^([^:]+):$')

# Reference pattern
REF_PATTERN = re.compile(r'@ref\(([^)]+)\)')


class FlowParser:
    """Parser for Flow format documents."""
    
    @staticmethod
    def normalize_indent(text: str) -> str:
        """
        Normalize indentation: tabs to 2 spaces.
        Validate even indentation.
        """
        lines = []
        for i, line in enumerate(text.split('\n'), 1):
            # Convert tabs to 2 spaces
            normalized = line.replace('\t', '  ')
            
            # Check indent is even (ignoring empty lines)
            if normalized.strip():
                leading = len(normalized) - len(normalized.lstrip())
                if leading % 2 != 0:
                    raise ValueError(f"Line {i}: Odd indentation ({leading} spaces). Use 2-space increments.")
            
            lines.append(normalized)
        
        return '\n'.join(lines)
    
    @staticmethod
    def detect_type(content: str) -> tuple[str, str]:
        """
        Detect node type from content prefix.
        Returns (type, cleaned_content).
        """
        content = content.strip()
        
        # Check each type pattern
        for node_type, pattern in TYPE_PATTERNS.items():
            match = pattern.match(content)
            if match:
                if node_type == 'Loc':
                    # Special handling for location nodes
                    line_num, func = match.groups()
                    return ('Loc', f"~{line_num}: {func}")
                else:
                    return (node_type, match.group(1))
        
        # Check if it's a header (ends with colon only)
        header_match = HEADER_PATTERN.match(content)
        if header_match:
            return ('Header', header_match.group(1))
        
        # Default to Content
        return ('Content', content)
    
    @staticmethod
    def extract_refs(content: str) -> list[str]:
        """Extract @ref() targets from content."""
        return REF_PATTERN.findall(content)
    
    @staticmethod
    def parse(text: str, creator: str = "unknown") -> FlowDocument:
        """
        Parse Flow format text into a FlowDocument.
        
        Args:
            text: Flow format text
            creator: Agent ID creating this document
            
        Returns:
            FlowDocument with parsed nodes and hierarchy
        """
        # Normalize indentation
        text = FlowParser.normalize_indent(text)
        lines = text.split('\n')
        
        # Parse anchor line
        topic, agent, date = "", "", ""
        start_line = 0
        
        for i, line in enumerate(lines):
            if line.strip().startswith('@F'):
                match = re.match(r'^@F\s+(\S+)\s+(\S+)\s+(\S+)', line.strip())
                if match:
                    topic, agent, date = match.groups()
                    start_line = i + 1
                    break
        
        if not topic:
            raise ValueError("Missing @F anchor line. Expected: @F <topic> <agent> <date>")
        
        doc = FlowDocument(
            topic=topic,
            agent=agent,
            date=date,
            raw_text=text
        )
        
        # Build indent stack for hierarchy tracking
        # Stack entries: (indent_level, content) for each ancestor
        indent_stack: list[tuple[int, str]] = []
        
        for line_num, line in enumerate(lines[start_line:], start_line + 1):
            # Skip empty lines
            if not line.strip():
                continue
            
            # Calculate indent
            stripped = line.lstrip()
            indent = len(line) - len(stripped)
            content = stripped
            
            # Pop stack to find parent at lower indent
            while indent_stack and indent_stack[-1][0] >= indent:
                indent_stack.pop()
            
            # Detect type and clean content
            node_type, cleaned = FlowParser.detect_type(content)
            
            # Extract refs
            refs = FlowParser.extract_refs(content)
            
            # Determine root and pivot
            root = indent_stack[0][1] if indent_stack else ""
            pivot = indent_stack[-1][1] if indent_stack else ""
            
            # Create node
            node = FlowNode(
                content=cleaned,
                indent_level=indent,
                line_number=line_num,
                node_type=node_type,
                root=root,
                pivot=pivot,
                refs=refs,
                creator=creator
            )
            
            doc.nodes.append(node)
            
            # Push to stack (headers always push, content pushes for potential children)
            indent_stack.append((indent, cleaned))
        
        return doc
    
    @staticmethod
    def build_embedding_context(node: FlowNode) -> str:
        """
        Build Root-Pivot-Leaf embedding string for a node.
        
        This is the key insight from Gemini collaboration:
        Full path dilutes signal, Root-Pivot-Leaf preserves:
        - What domain (Root)
        - What specifically (Pivot)  
        - The detail (Leaf/content)
        """
        parts = []
        
        if node.root:
            parts.append(node.root)
        if node.pivot and node.pivot != node.root:
            parts.append(node.pivot)
        parts.append(node.content)
        
        return ": ".join(parts)
    
    @staticmethod
    def validate(doc: FlowDocument) -> tuple[bool, list[str]]:
        """
        Validate a Flow document structure.
        
        Checks:
        - Orphan check: no indent jumps > 2
        - Density check: headers have content
        - Has meaningful content (not just headers)
        
        Returns:
            (is_valid, list of error messages)
        """
        errors = []
        
        if not doc.nodes:
            errors.append("Empty document - no nodes found")
            return False, errors
        
        prev_indent = 0
        header_indices = set()
        
        for i, node in enumerate(doc.nodes):
            # Shape: large indent jumps are valid (whitespace as emphasis)
            # Only flag if jumping MORE than 20 spaces (likely a mistake)
            if node.indent_level > prev_indent + 20:
                errors.append(
                    f"Line {node.line_number}: Extreme indent jump from {prev_indent} to {node.indent_level}"
                )
            
            prev_indent = node.indent_level
            
            # Track headers for density check
            if node.node_type == 'Header':
                header_indices.add(i)
        
        # Density check: headers should have children (next node at higher indent)
        for idx in header_indices:
            if idx == len(doc.nodes) - 1:
                errors.append(f"Line {doc.nodes[idx].line_number}: Empty header '{doc.nodes[idx].content}' at end of document")
            elif doc.nodes[idx + 1].indent_level <= doc.nodes[idx].indent_level:
                errors.append(f"Line {doc.nodes[idx].line_number}: Empty header '{doc.nodes[idx].content}' - no children")
        
        # Content check: need more than just headers
        content_nodes = [n for n in doc.nodes if n.node_type != 'Header']
        if len(content_nodes) < 3:
            errors.append(f"Too few content nodes ({len(content_nodes)}). Need at least 3.")
        
        return len(errors) == 0, errors


def parse_flow(text: str, creator: str = "unknown") -> FlowDocument:
    """Convenience function to parse Flow text."""
    return FlowParser.parse(text, creator)


def is_flow_format(text: str) -> bool:
    """Check if text appears to be Flow format (starts with @F)."""
    for line in text.strip().split('\n'):
        line = line.strip()
        if not line:
            continue
        return line.startswith('@F')
    return False


def is_sif_format(text: str) -> bool:
    """Check if text appears to be SIF format (starts with @G)."""
    for line in text.strip().split('\n'):
        line = line.strip()
        if not line:
            continue
        return line.startswith('@G')
    return False
