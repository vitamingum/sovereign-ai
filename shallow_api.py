"""Instant CLI/API entry point finder from AST - no LLM, sub-second results."""

import ast
import sys
from pathlib import Path
from table import render_table

def find_entry_points(filepath: Path) -> dict:
    """Find CLI entry points and public functions."""
    try:
        content = filepath.read_text(encoding='utf-8-sig')
        tree = ast.parse(content)
    except (SyntaxError, UnicodeDecodeError, PermissionError):
        return {}
    
    result = {
        'has_main': False,
        'has_argparse': False,
        'cli_args': [],
        'public_funcs': [],
    }
    
    for node in ast.walk(tree):
        # Check for if __name__ == '__main__'
        if isinstance(node, ast.If):
            if isinstance(node.test, ast.Compare):
                if isinstance(node.test.left, ast.Name) and node.test.left.id == '__name__':
                    result['has_main'] = True
        
        # Check for argparse
        if isinstance(node, ast.Import):
            for alias in node.names:
                if alias.name == 'argparse':
                    result['has_argparse'] = True
        if isinstance(node, ast.ImportFrom):
            if node.module == 'argparse':
                result['has_argparse'] = True
        
        # Find add_argument calls for CLI args
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Attribute):
                if node.func.attr == 'add_argument':
                    for arg in node.args:
                        if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                            if arg.value.startswith('-'):
                                result['cli_args'].append(arg.value)
                            break
        
        # Find public functions (no leading underscore)
        if isinstance(node, ast.FunctionDef):
            if not node.name.startswith('_') and node.name != 'main':
                result['public_funcs'].append(node.name)
    
    return result

def main():
    import argparse
    parser = argparse.ArgumentParser(description='Find CLI entry points and public APIs')
    parser.add_argument('files', nargs='*', help='Files to analyze')
    parser.add_argument('-d', '--directory', help='Analyze all .py files in directory')
    parser.add_argument('--cli', action='store_true', help='Show only CLI tools')
    args = parser.parse_args()
    
    # Gather files
    files = []
    if args.directory:
        files = list(Path(args.directory).glob('*.py'))
    elif args.files:
        files = [Path(f) for f in args.files]
    else:
        files = list(Path('.').glob('*.py'))
    
    if not files:
        print("No Python files found")
        sys.exit(1)
    
    rows = []
    for f in files:
        info = find_entry_points(f)
        if not info:
            continue
        
        # Skip non-CLI if --cli specified
        if args.cli and not info['has_main']:
            continue
        
        entry = '✓ CLI' if info['has_main'] else ''
        if info['has_argparse']:
            entry += ' (argparse)'
        
        cli_args = ', '.join(info['cli_args'][:5])  # First 5 args
        if len(info['cli_args']) > 5:
            cli_args += f' (+{len(info["cli_args"])-5})'
        
        if info['has_main'] or info['public_funcs']:
            rows.append([
                f.stem,
                entry,
                cli_args or '-',
                str(len(info['public_funcs']))
            ])
    
    if not rows:
        print("No entry points found")
        return
    
    print(render_table(
        headers=['Module', 'Entry', 'CLI Args', 'Public Fns'],
        rows=sorted(rows, key=lambda x: (x[1] == '', x[0])),  # CLI first
        style='rounded'
    ))

if __name__ == '__main__':
    main()
