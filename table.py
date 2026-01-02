#!/usr/bin/env python3
"""
table.py - Transform natural language into beautiful tables.

Usage:
    python table.py "your natural language description"
    python table.py -f file.txt
    echo "data" | python table.py

Examples:
    python table.py "agents: opus, gemini, grok. status: active, sleeping, active"
    python table.py "name alice age 30, name bob age 25, name carol age 35"
    python table.py "monday: gym, coding. tuesday: reading, rest. wednesday: writing"
    python table.py "task build-mirror status done, task write-tests status pending"

The tool uses a local LLM to parse your input and render it as a
beautifully formatted table with box-drawing characters.
"""

import sys
import json
import requests
from typing import Optional


# ─────────────────────────────────────────────────────────────────────────────
# Table Rendering (pure Python, no dependencies)
# ─────────────────────────────────────────────────────────────────────────────

class BoxChars:
    """Unicode box-drawing characters for beautiful tables."""
    # Light box
    LIGHT = {
        'tl': '┌', 'tr': '┐', 'bl': '└', 'br': '┘',
        'h': '─', 'v': '│',
        'lt': '├', 'rt': '┤', 'tt': '┬', 'bt': '┴', 'cross': '┼'
    }
    # Heavy box (for headers)
    HEAVY = {
        'tl': '┏', 'tr': '┓', 'bl': '┗', 'br': '┛',
        'h': '━', 'v': '┃',
        'lt': '┣', 'rt': '┫', 'tt': '┳', 'bt': '┻', 'cross': '╋'
    }
    # Double line
    DOUBLE = {
        'tl': '╔', 'tr': '╗', 'bl': '╚', 'br': '╝',
        'h': '═', 'v': '║',
        'lt': '╠', 'rt': '╣', 'tt': '╦', 'bt': '╩', 'cross': '╬'
    }
    # Rounded corners
    ROUNDED = {
        'tl': '╭', 'tr': '╮', 'bl': '╰', 'br': '╯',
        'h': '─', 'v': '│',
        'lt': '├', 'rt': '┤', 'tt': '┬', 'bt': '┴', 'cross': '┼'
    }


def render_table(headers: list[str], rows: list[list[str]], style: str = 'rounded') -> str:
    """
    Render a beautiful Unicode table.
    
    Args:
        headers: Column headers
        rows: List of rows, each row is a list of cell values
        style: 'light', 'heavy', 'double', or 'rounded'
    
    Returns:
        Formatted table as a string
    """
    box = getattr(BoxChars, style.upper(), BoxChars.ROUNDED)
    
    # Calculate column widths (minimum 3, pad for aesthetics)
    num_cols = len(headers)
    widths = [max(3, len(h) + 2) for h in headers]
    
    for row in rows:
        for i, cell in enumerate(row):
            if i < num_cols:
                widths[i] = max(widths[i], len(str(cell)) + 2)
    
    def make_line(left: str, mid: str, right: str, fill: str) -> str:
        return left + mid.join(fill * w for w in widths) + right
    
    def make_row(cells: list[str], sep: str) -> str:
        padded = []
        for i, cell in enumerate(cells):
            if i < len(widths):
                padded.append(f" {str(cell):<{widths[i]-2}} ")
        return sep + sep.join(padded) + sep
    
    lines = []
    
    # Top border
    lines.append(make_line(box['tl'], box['tt'], box['tr'], box['h']))
    
    # Header row
    lines.append(make_row(headers, box['v']))
    
    # Header separator (slightly heavier feel)
    lines.append(make_line(box['lt'], box['cross'], box['rt'], box['h']))
    
    # Data rows
    for row in rows:
        # Pad row to match header count
        padded_row = list(row) + [''] * (num_cols - len(row))
        lines.append(make_row(padded_row[:num_cols], box['v']))
    
    # Bottom border
    lines.append(make_line(box['bl'], box['bt'], box['br'], box['h']))
    
    return '\n'.join(lines)


# ─────────────────────────────────────────────────────────────────────────────
# LLM Parsing
# ─────────────────────────────────────────────────────────────────────────────

PARSE_PROMPT = '''Parse this natural language into a JSON table structure.
Return ONLY valid JSON with this exact format:
{"headers": ["col1", "col2", ...], "rows": [["val1", "val2", ...], ...]}

Be smart about inferring structure. Examples:
- "alice 30, bob 25" → {"headers": ["Name", "Value"], "rows": [["alice", "30"], ["bob", "25"]]}
- "name alice age 30, name bob age 25" → {"headers": ["Name", "Age"], "rows": [["alice", "30"], ["bob", "25"]]}
- "agents: opus, gemini. status: active, sleeping" → {"headers": ["Agent", "Status"], "rows": [["opus", "active"], ["gemini", "sleeping"]]}
- "monday gym coding, tuesday reading" → {"headers": ["Day", "Activities"], "rows": [["monday", "gym, coding"], ["tuesday", "reading"]]}

Input to parse:
'''


def parse_with_ollama(text: str, model: str = 'qwen2.5:7b') -> Optional[dict]:
    """Parse natural language to table structure using Ollama."""
    try:
        response = requests.post(
            'http://localhost:11434/api/generate',
            json={
                'model': model,
                'prompt': PARSE_PROMPT + text,
                'stream': False,
                'options': {'temperature': 0},
                'format': 'json'
            },
            timeout=30
        )
        result = response.json().get('response', '')
        
        # Extract JSON from response
        if '{' in result and '}' in result:
            json_str = result[result.find('{'):result.rfind('}')+1]
            return json.loads(json_str)
    except Exception as e:
        print(f"LLM parse failed: {e}", file=sys.stderr)
    return None


def fallback_parse(text: str) -> dict:
    """Simple fallback parser for common patterns."""
    lines = [l.strip() for l in text.strip().split('\n') if l.strip()]
    
    if not lines:
        return {"headers": ["Value"], "rows": [[text]]}
    
    # Check for delimiter patterns
    for delim in ['\t', '|', ',', ';']:
        if delim in lines[0]:
            parts = [l.split(delim) for l in lines]
            parts = [[c.strip() for c in row] for row in parts]
            if len(parts) > 1:
                # First line might be headers
                return {"headers": parts[0], "rows": parts[1:]}
            else:
                return {"headers": [f"Col{i+1}" for i in range(len(parts[0]))], "rows": parts}
    
    # Simple key-value pairs
    if ':' in text:
        pairs = []
        for part in text.replace('\n', ', ').split(','):
            if ':' in part:
                k, v = part.split(':', 1)
                pairs.append([k.strip(), v.strip()])
        if pairs:
            return {"headers": ["Key", "Value"], "rows": pairs}
    
    # Just wrap as single column
    return {"headers": ["Item"], "rows": [[l] for l in lines]}


# ─────────────────────────────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────────────────────────────

def main():
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Transform natural language into beautiful tables',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
Examples:
  python table.py "alice 30, bob 25, carol 35"
  python table.py "task: build, status: done | task: test, status: pending"
  python table.py -f data.txt
  python table.py --style double "name age city; alice 30 nyc; bob 25 la"
'''
    )
    parser.add_argument('text', nargs='?', help='Natural language to tablify')
    parser.add_argument('-f', '--file', help='Read input from file')
    parser.add_argument('-s', '--style', default='rounded',
                       choices=['light', 'heavy', 'double', 'rounded'],
                       help='Table border style (default: rounded)')
    parser.add_argument('--no-llm', action='store_true',
                       help='Use simple parser without LLM')
    parser.add_argument('--model', default='qwen2.5:7b',
                       help='Ollama model to use (default: qwen2.5:7b)')
    
    args = parser.parse_args()
    
    # Get input
    if args.file:
        with open(args.file, 'r', encoding='utf-8') as f:
            text = f.read().strip()
    elif args.text:
        text = args.text
    elif not sys.stdin.isatty():
        text = sys.stdin.read().strip()
    else:
        print("Usage: python table.py \"your description\"", file=sys.stderr)
        print("       python table.py -f file.txt", file=sys.stderr)
        print("       echo \"data\" | python table.py", file=sys.stderr)
        sys.exit(1)
    
    if not text:
        print("No input provided", file=sys.stderr)
        sys.exit(1)
    
    # Parse
    data = None
    if not args.no_llm:
        data = parse_with_ollama(text, args.model)
    
    if not data:
        data = fallback_parse(text)
    
    # Validate
    if not data.get('headers') or not data.get('rows'):
        print("Could not parse input into table format", file=sys.stderr)
        sys.exit(1)
    
    # Render
    table = render_table(data['headers'], data['rows'], args.style)
    print(table)


if __name__ == '__main__':
    main()
