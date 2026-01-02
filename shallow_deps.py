"""Instant import dependency graph from AST - no LLM, sub-second results."""

import ast
import sys
from pathlib import Path
from collections import defaultdict
from table import render_table

def extract_imports(filepath: Path) -> tuple[set[str], set[str]]:
    """Extract stdlib/external and local imports from a Python file."""
    try:
        tree = ast.parse(filepath.read_text(encoding='utf-8'))
    except (SyntaxError, UnicodeDecodeError):
        return set(), set()
    
    stdlib_external = set()
    local = set()
    
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                module = alias.name.split('.')[0]
                stdlib_external.add(module)
        elif isinstance(node, ast.ImportFrom):
            if node.module:
                module = node.module.split('.')[0]
                # Heuristic: if it matches a local file/folder, it's local
                if node.level > 0:  # relative import
                    local.add(node.module)
                else:
                    stdlib_external.add(module)
    
    return stdlib_external, local

def find_local_modules(directory: Path) -> set[str]:
    """Find all local Python module names in directory."""
    modules = set()
    for f in directory.glob('*.py'):
        modules.add(f.stem)
    for d in directory.iterdir():
        if d.is_dir() and (d / '__init__.py').exists():
            modules.add(d.name)
    return modules

def build_dep_graph(files: list[Path], project_root: Path = None) -> dict:
    """Build dependency graph for given files."""
    if project_root is None:
        project_root = files[0].parent if files else Path('.')
    
    local_modules = find_local_modules(project_root)
    
    graph = {}
    for f in files:
        stdlib_ext, local = extract_imports(f)
        
        # Reclassify: if stdlib_ext item matches local module, it's local
        actual_local = local.copy()
        actual_external = set()
        for mod in stdlib_ext:
            if mod in local_modules:
                actual_local.add(mod)
            else:
                actual_external.add(mod)
        
        graph[f.stem] = {
            'external': sorted(actual_external),
            'local': sorted(actual_local)
        }
    
    return graph

def render_graph(graph: dict, style: str = 'tree') -> str:
    """Render dependency graph as text."""
    lines = []
    
    if style == 'tree':
        for module, deps in sorted(graph.items()):
            lines.append(f"╭─ {module}")
            if deps['local']:
                lines.append(f"│  ├─ local: {', '.join(deps['local'])}")
            if deps['external']:
                lines.append(f"│  └─ external: {', '.join(deps['external'])}")
            lines.append("╰" + "─" * 40)
    
    elif style == 'matrix':
        # Who imports whom (local only)
        all_modules = set(graph.keys())
        for mod in graph.values():
            all_modules.update(mod['local'])
        all_modules = sorted(all_modules)
        
        # Header
        max_name = max(len(m) for m in all_modules) if all_modules else 10
        header = ' ' * (max_name + 2) + '  '.join(m[:3] for m in all_modules)
        lines.append(header)
        lines.append('─' * len(header))
        
        for mod in all_modules:
            row = f"{mod:<{max_name}}  "
            for target in all_modules:
                if mod in graph and target in graph[mod]['local']:
                    row += ' → '
                elif mod == target:
                    row += ' · '
                else:
                    row += '   '
                row += ' '
            lines.append(row)
    
    elif style == 'dot':
        lines.append('digraph deps {')
        lines.append('  rankdir=LR;')
        lines.append('  node [shape=box];')
        for module, deps in graph.items():
            for local_dep in deps['local']:
                lines.append(f'  "{module}" -> "{local_dep}";')
        lines.append('}')
    
    return '\n'.join(lines)

def render_reverse(graph: dict) -> str:
    """Show what depends on each module (reverse deps) as a table."""
    reverse = defaultdict(list)
    for module, deps in graph.items():
        for local_dep in deps['local']:
            reverse[local_dep].append(module)
    
    if not reverse:
        return "  (no local dependencies found)"
    
    # Build table data
    rows = []
    for module in sorted(reverse.keys()):
        dependents = reverse[module]
        rows.append([module, ', '.join(sorted(dependents)), str(len(dependents))])
    
    return render_table(
        headers=['Module', 'Depended on by', 'Count'],
        rows=rows,
        style='rounded'
    )

def main():
    import argparse
    parser = argparse.ArgumentParser(description='Instant import dependency graph')
    parser.add_argument('files', nargs='*', help='Python files to analyze')
    parser.add_argument('-d', '--directory', help='Analyze all .py files in directory')
    parser.add_argument('-s', '--style', choices=['tree', 'matrix', 'dot'], 
                        default='tree', help='Output style')
    parser.add_argument('-r', '--reverse', action='store_true',
                        help='Show reverse dependencies (what depends on X)')
    parser.add_argument('--hubs', action='store_true',
                        help='Show most connected modules (high in/out degree)')
    parser.add_argument('-e', '--external', action='store_true',
                        help='Include external dependencies in analysis')
    args = parser.parse_args()
    
    # Gather files
    files = []
    project_root = Path('.')
    
    if args.directory:
        project_root = Path(args.directory)
        files = list(project_root.glob('*.py'))
    elif args.files:
        files = [Path(f) for f in args.files]
        project_root = files[0].parent
    else:
        # Default: current directory
        files = list(Path('.').glob('*.py'))
    
    if not files:
        print("No Python files found")
        sys.exit(1)
    
    graph = build_dep_graph(files, project_root)
    
    # Smart default: hubs for whole project, tree for specific files
    show_hubs = args.hubs or (not args.files and not args.reverse and args.style == 'tree')
    
    if show_hubs and not args.reverse:
        # Calculate in-degree (depended on) and out-degree (depends on)
        in_degree = defaultdict(int)
        out_degree = defaultdict(int)
        for module, deps in graph.items():
            out_degree[module] = len(deps['local'])
            for local_dep in deps['local']:
                in_degree[local_dep] += 1
        
        # Combine and sort by total degree
        all_modules = set(graph.keys()) | set(in_degree.keys())
        rows = []
        for mod in all_modules:
            in_d = in_degree.get(mod, 0)
            out_d = out_degree.get(mod, 0)
            total = in_d + out_d
            if total > 0:  # Only show connected modules
                role = '🔌 hub' if in_d >= 2 else ('📡 leaf' if in_d == 0 and out_d > 0 else '')
                rows.append([mod, str(in_d), str(out_d), str(total), role])
        
        rows.sort(key=lambda x: -int(x[3]))  # Sort by total desc
        print(render_table(
            headers=['Module', 'In', 'Out', 'Total', 'Role'],
            rows=rows,
            style='rounded'
        ))
    elif args.reverse:
        print(render_reverse(graph))
    else:
        print(render_graph(graph, args.style))

if __name__ == '__main__':
    main()
