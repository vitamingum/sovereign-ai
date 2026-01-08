#!/usr/bin/env python3
"""
sif_to_flow.py - Convert SIF format to Flow format

Read-only converter: parses SIF, outputs Flow. Does NOT modify enclave storage.
This is a one-time migration tool following the "dumb converter" philosophy:
- Scripts do math, agents do judgment
- Mechanical 1:1 transformation, no smart optimizations
- Agents garden the output afterward

Usage:
    py sif_to_flow.py input.sif                    # Output to stdout
    py sif_to_flow.py input.sif -o output.flow     # Output to file
    py sif_to_flow.py --stdin                      # Read from stdin
"""

import sys
import re
import argparse
from dataclasses import dataclass, field
from typing import Optional


@dataclass
class Node:
    """Represents a SIF node"""
    index: int  # 1-based index for _N references
    node_type: str
    content: str
    children: list = field(default_factory=list)
    refs: list = field(default_factory=list)  # Non-containment edges as @ref
    parent_idx: Optional[int] = None
    section: str = ""  # # Section comment this node belongs to


@dataclass 
class Edge:
    """Represents a SIF edge"""
    source: int  # 1-based node index
    relation: str
    target: int  # 1-based node index


# Edge relations that indicate containment (become indentation)
CONTAINMENT_RELATIONS = {
    'contains', 'has', 'includes', 'defined_in', 'implements',
    'part_of', 'belongs_to', 'child_of'
}


def parse_sif(text: str) -> tuple[dict, list[Node], list[Edge], str]:
    """
    Parse SIF text into anchor info, nodes, and edges.
    
    Returns:
        anchor: dict with topic, agent, date
        nodes: list of Node objects (1-indexed)
        edges: list of Edge objects
        raw_sections: dict mapping node index to section name
    """
    lines = text.strip().split('\n')
    
    anchor = {'topic': '', 'agent': '', 'date': ''}
    nodes = [None]  # 1-indexed, position 0 is placeholder
    edges = []
    current_section = ""
    
    # Regex patterns
    anchor_pattern = re.compile(r'^@G\s+(\S+)\s+(\S+)\s+(\S+)')
    node_pattern = re.compile(r'^N\s+(\w+)\s+[\'"](.+)[\'"]$')
    edge_pattern = re.compile(r'^E\s+_(\d+)\s+(\w+)\s+_(\d+)$')
    section_pattern = re.compile(r'^#\s*(.+)$')
    
    for line in lines:
        line = line.rstrip()
        
        if not line:
            continue
            
        # Parse anchor
        anchor_match = anchor_pattern.match(line)
        if anchor_match:
            anchor['topic'] = anchor_match.group(1)
            anchor['agent'] = anchor_match.group(2)
            anchor['date'] = anchor_match.group(3)
            continue
        
        # Track section comments
        section_match = section_pattern.match(line)
        if section_match:
            current_section = section_match.group(1).strip()
            continue
        
        # Parse node
        node_match = node_pattern.match(line)
        if node_match:
            node_type = node_match.group(1)
            content = node_match.group(2)
            node = Node(
                index=len(nodes),
                node_type=node_type,
                content=content,
                section=current_section
            )
            nodes.append(node)
            continue
        
        # Parse edge
        edge_match = edge_pattern.match(line)
        if edge_match:
            source = int(edge_match.group(1))
            relation = edge_match.group(2)
            target = int(edge_match.group(3))
            edges.append(Edge(source=source, relation=relation, target=target))
            continue
    
    return anchor, nodes, edges


def build_tree(nodes: list[Node], edges: list[Edge]) -> list[int]:
    """
    Build tree structure from containment edges.
    
    Returns list of root node indices (nodes with no parent).
    """
    # Find containment edges and set parent relationships
    for edge in edges:
        if edge.relation.lower() in CONTAINMENT_RELATIONS:
            if 1 <= edge.source < len(nodes) and 1 <= edge.target < len(nodes):
                parent_node = nodes[edge.source]
                child_node = nodes[edge.target]
                
                # Parent contains child, so child's parent is source
                if edge.relation.lower() in {'contains', 'has', 'includes'}:
                    child_node.parent_idx = edge.source
                    parent_node.children.append(edge.target)
                # Child implements/belongs_to parent
                elif edge.relation.lower() in {'implements', 'part_of', 'belongs_to', 'child_of', 'defined_in'}:
                    child_node.parent_idx = edge.target
                    if child_node.index not in nodes[edge.target].children:
                        nodes[edge.target].children.append(child_node.index)
        else:
            # Non-containment edges: only keep meaningful cross-references
            # Skip edges that just describe relationships within the document
            # (most SIF edges are structural, not semantic cross-references)
            pass  # Dumb converter: drop non-containment edges, agents add @ref manually if needed
    
    # Find roots (nodes with no parent)
    roots = []
    for i, node in enumerate(nodes):
        if node is None:
            continue
        if node.parent_idx is None:
            roots.append(i)
    
    return roots


def format_node_content(node: Node) -> str:
    """
    Format a node's content for Flow output.
    
    Converts SIF node types to Flow-appropriate formatting.
    """
    content = node.content
    node_type = node.node_type
    
    # Type-specific formatting
    type_prefixes = {
        'S': 'Summary: ',
        'P': 'Purpose: ',
        'D': 'Design: ',
        'G': 'Gotcha: ',
        'I': 'Insight: ',
        'Q': 'Question: ',
        'M': 'Metric: ',
        'C': 'Component: ',
        'Loc': '~',
        'Sig': 'Signature: ',
        'Flow': 'Flow: ',
        'Cmd': 'Command: ',
        'Example': 'Example: ',
        'Principle': 'Principle: ',
        'Problem': 'Problem: ',
        'Spec': 'Spec: ',
        'Phase': 'Phase: ',
        'Order': '',
        'Decision': 'Decision: ',
        'Breakthrough': 'Breakthrough: ',
        'Insight': 'Insight: ',
        'Workflow': 'Workflow: ',
        'Trap': 'Trap: ',
        'Audit': 'Audit: ',
        'Research': 'Research: ',
        'Agent': 'Agent: ',
    }
    
    prefix = type_prefixes.get(node_type, f'{node_type}: ')
    
    # Special handling for Loc nodes - they use ~line format
    if node_type == 'Loc':
        # Try to extract line number
        line_match = re.search(r'~?line\s*(\d+)', content, re.IGNORECASE)
        func_match = re.search(r'(\w+\.\w+)\s+(\w+\([^)]*\))', content)
        if line_match and func_match:
            return f"~{line_match.group(1)}: {func_match.group(2)}"
        elif line_match:
            return f"~{line_match.group(1)}: {content.split('~')[0].strip()}"
        else:
            return f"~{content}"
    
    return f"{prefix}{content}"


def node_to_flow(node: Node, nodes: list[Node], indent: int = 0) -> list[str]:
    """
    Convert a node and its children to Flow format lines.
    
    Args:
        node: The node to convert
        nodes: Full node list for resolving children
        indent: Current indentation level (in spaces)
    
    Returns:
        List of formatted lines
    """
    lines = []
    prefix = "  " * (indent // 2)  # 2-space indent
    
    # Format this node's content
    content = format_node_content(node)
    
    lines.append(f"{prefix}{content}")
    
    # Recursively add children
    for child_idx in node.children:
        if 1 <= child_idx < len(nodes) and nodes[child_idx] is not None:
            child_lines = node_to_flow(nodes[child_idx], nodes, indent + 2)
            lines.extend(child_lines)
    
    return lines


def sif_to_flow(text: str) -> str:
    """
    Convert SIF text to Flow format.
    
    Main conversion function.
    """
    anchor, nodes, edges = parse_sif(text)
    roots = build_tree(nodes, edges)
    
    # Start output with Flow anchor
    output_lines = [
        f"@F {anchor['topic']} {anchor['agent']} {anchor['date']}",
        ""
    ]
    
    # Group nodes by section for orphans
    sections = {}
    for i, node in enumerate(nodes):
        if node is None:
            continue
        section = node.section or "Uncategorized"
        if section not in sections:
            sections[section] = []
        sections[section].append(i)
    
    # Process nodes section by section
    processed = set()
    
    for section_name, section_nodes in sections.items():
        section_has_content = False
        section_lines = []
        
        for node_idx in section_nodes:
            if node_idx in processed:
                continue
            
            node = nodes[node_idx]
            if node is None:
                continue
            
            # Only process root nodes of this section (or orphans)
            if node.parent_idx is None:
                if not section_has_content:
                    section_lines.append(f"{section_name}:")
                    section_has_content = True
                
                # Convert node and children
                node_lines = node_to_flow(node, nodes, indent=2)
                section_lines.extend(node_lines)
                
                # Mark this subtree as processed
                def mark_processed(idx):
                    processed.add(idx)
                    if 1 <= idx < len(nodes) and nodes[idx]:
                        for child in nodes[idx].children:
                            mark_processed(child)
                mark_processed(node_idx)
        
        if section_has_content:
            output_lines.extend(section_lines)
            output_lines.append("")  # Blank line between sections
    
    return '\n'.join(output_lines)


def main():
    parser = argparse.ArgumentParser(
        description='Convert SIF format to Flow format',
        epilog='Read-only converter. Does not modify enclave storage.'
    )
    parser.add_argument('input', nargs='?', help='Input SIF file')
    parser.add_argument('-o', '--output', help='Output file (default: stdout)')
    parser.add_argument('--stdin', action='store_true', help='Read from stdin')
    
    args = parser.parse_args()
    
    # Read input
    if args.stdin or args.input == '-':
        text = sys.stdin.read()
    elif args.input:
        with open(args.input, 'r', encoding='utf-8') as f:
            text = f.read()
    else:
        parser.print_help()
        sys.exit(1)
    
    # Convert
    flow_output = sif_to_flow(text)
    
    # Write output
    if args.output:
        with open(args.output, 'w', encoding='utf-8') as f:
            f.write(flow_output)
        print(f"✅ Converted to {args.output}")
    else:
        print(flow_output)


if __name__ == '__main__':
    main()
