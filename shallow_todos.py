"""Instant TODO/FIXME/HACK finder from source code - no LLM, sub-second results."""

import ast
import re
import sys
from pathlib import Path
from table import render_table

# Patterns to find
PATTERNS = {
    'TODO': re.compile(r'#\s*TODO[:\s]*(.*)', re.IGNORECASE),
    'FIXME': re.compile(r'#\s*FIXME[:\s]*(.*)', re.IGNORECASE),
    'HACK': re.compile(r'#\s*HACK[:\s]*(.*)', re.IGNORECASE),
    'XXX': re.compile(r'#\s*XXX[:\s]*(.*)', re.IGNORECASE),
    'NOTE': re.compile(r'#\s*NOTE[:\s]*(.*)', re.IGNORECASE),
}

def scan_file(filepath: Path) -> list[tuple[str, int, str, str]]:
    """Scan file for TODO-style comments. Returns (file, line, type, text)."""
    results = []
    try:
        content = filepath.read_text(encoding='utf-8-sig')
    except (UnicodeDecodeError, PermissionError):
        return results
    
    for lineno, line in enumerate(content.split('\n'), 1):
        for tag, pattern in PATTERNS.items():
            match = pattern.search(line)
            if match:
                text = match.group(1).strip()[:60]  # Truncate
                results.append((filepath.name, lineno, tag, text))
                break  # Only one match per line
    
    return results

def main():
    import argparse
    parser = argparse.ArgumentParser(description='Find TODO/FIXME/HACK comments instantly')
    parser.add_argument('files', nargs='*', help='Files to scan')
    parser.add_argument('-d', '--directory', help='Scan all .py files in directory')
    parser.add_argument('-t', '--type', help='Filter by type (TODO, FIXME, HACK, XXX, NOTE)')
    parser.add_argument('--stats', action='store_true', help='Show summary stats only')
    args = parser.parse_args()
    
    # Gather files
    files = []
    if args.directory:
        files = list(Path(args.directory).rglob('*.py'))
    elif args.files:
        files = [Path(f) for f in args.files]
    else:
        files = list(Path('.').glob('*.py'))
    
    if not files:
        print("No Python files found")
        sys.exit(1)
    
    # Scan
    all_results = []
    for f in files:
        all_results.extend(scan_file(f))
    
    # Filter by type if specified
    if args.type:
        all_results = [r for r in all_results if r[2].upper() == args.type.upper()]
    
    if not all_results:
        print("✓ No TODOs/FIXMEs found")
        return
    
    if args.stats:
        # Summary only
        from collections import Counter
        by_type = Counter(r[2] for r in all_results)
        by_file = Counter(r[0] for r in all_results)
        
        print(render_table(
            headers=['Type', 'Count'],
            rows=[[t, str(c)] for t, c in by_type.most_common()],
            style='rounded'
        ))
        print()
        print(render_table(
            headers=['File', 'Count'],
            rows=[[f, str(c)] for f, c in by_file.most_common(10)],
            style='rounded'
        ))
    else:
        # Full table
        rows = [[r[0], str(r[1]), r[2], r[3]] for r in all_results]
        print(render_table(
            headers=['File', 'Line', 'Type', 'Text'],
            rows=rows,
            style='rounded'
        ))
        print(f"\n{len(all_results)} items found")

if __name__ == '__main__':
    main()
