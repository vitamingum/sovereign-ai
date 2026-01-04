#!/usr/bin/env python3
"""
shallow_understand.py - Instant codebase map from docstrings.

Usage:
    python shallow_understand.py *.py           # instant (default)
    python shallow_understand.py -d enclave/    # all .py in directory
    python shallow_understand.py --llm *.py     # deeper LLM analysis
    python shallow_understand.py --deep *.py    # thorough LLM analysis

Default mode parses docstrings and function signatures - no LLM, sub-second.
Outputs a beautiful table for quick orientation.

Use --llm or --deep when you need actual understanding vs just a map.
"""

import sys
import os
import json
import requests
import hashlib
import argparse
import subprocess
from pathlib import Path
from datetime import datetime, timezone
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Optional

# Cache for LLM responses
cache_file = Path(__file__).parent / ".shallow_cache.json"
cache = {}
if cache_file.exists():
    try:
        with open(cache_file, 'r', encoding='utf-8') as f:
            cache = json.load(f)
    except:
        cache = {}


# ─────────────────────────────────────────────────────────────────────────────
# LLM Prompts
# ─────────────────────────────────────────────────────────────────────────────

UNDERSTAND_PROMPT = '''You are analyzing code to create a knowledge graph. Read this file carefully, then output a SIF graph.

SIF FORMAT (auto-ID - nodes get _1, _2, _3... automatically):
@G <name> opus <date>
N <Type> '<content>' -> <relation> <target_id>   # inline edge optional
E _1 <relation> _2                                # or separate edge lines

EXAMPLE for a hypothetical "cache.py":
@G cache-understanding opus 2026-01-01
N P 'Speed up repeated lookups by storing results in memory'
N D 'LRU eviction - removes least recently used when full' -> implements _1
N C 'get() checks cache first, calls origin on miss' -> part_of _2
N C 'set() stores value and updates access time' -> part_of _2
N G 'Thread-unsafe - concurrent writes can corrupt' -> warns_about _3
N A 'Keys are hashable' -> assumed_by _3
N W 'LRU chosen over LFU because access patterns are temporal' -> motivated _2

NODE TYPES: Purpose, Design, Component, Gotcha, Assumption, Why, Failure_Mode
EDGE TYPES: implements, part_of, motivated, feeds, warns_about, assumed_by, detail_of, fallback_for

NOW analyze this actual file. Create 8-15 nodes with SPECIFIC content about THIS code:

FILE: {filename}
```
{content}
```

Output ONLY the SIF (starting with @G, no markdown fences):'''

DEEP_PROMPT = '''Do a thorough analysis of this code. Generate comprehensive SIF.

Focus especially on:
1. The REAL purpose (not the obvious surface purpose)
2. Design trade-offs and why they were made
3. Every gotcha and edge case you can find
4. Assumptions that could break
5. How this interacts with other parts of a system

OUTPUT FORMAT - Return ONLY the SIF block:
```
@G {filename}-deep opus {date}
N P 'core motivation'
N D 'key design decision' -> implements _1
...
```

FILE: {filename}
CONTENT:
{content}
'''


import re
import ast

def instant_understand(filepath: str) -> tuple[str, list[str]]:
    """
    Instant understanding - no LLM, just parse docstrings and signatures.
    Returns (module_docstring, list_of_function_names).
    """
    content = read_file(filepath)
    
    # Try AST parsing for accurate extraction
    try:
        tree = ast.parse(content)
        
        # Module docstring
        doc = ast.get_docstring(tree) or ""
        # First line of docstring as purpose
        purpose = doc.split('\n')[0].strip() if doc else "(no docstring)"
        
        # Function/class names
        names = []
        for node in ast.walk(tree):
            if isinstance(node, ast.FunctionDef):
                names.append(f"def {node.name}()")
            elif isinstance(node, ast.ClassDef):
                names.append(f"class {node.name}")
        
        return purpose, names[:10]  # Cap at 10
        
    except SyntaxError:
        # Fallback: regex
        doc_match = re.search(r'^"""(.*?)"""', content, re.DOTALL)
        purpose = doc_match.group(1).split('\n')[0].strip() if doc_match else "(parse error)"
        
        funcs = re.findall(r'^def (\w+)\(', content, re.MULTILINE)[:10]
        classes = re.findall(r'^class (\w+)', content, re.MULTILINE)[:5]
        
        names = [f"class {c}" for c in classes] + [f"def {f}()" for f in funcs]
        return purpose, names


def get_file_hash(filepath: str) -> str:
    """Get first 12 chars of file hash."""
    with open(filepath, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()[:12]


def read_file(filepath: str) -> str:
    """Read file with fallback encodings."""
    for enc in ['utf-8-sig', 'utf-8', 'latin-1']:
        try:
            with open(filepath, 'r', encoding=enc) as f:
                return f.read()
        except UnicodeDecodeError:
            continue
    raise ValueError(f"Could not decode {filepath}")


def generate_sif(filepath: str, model: str = 'qwen2.5:7b', deep: bool = False) -> Optional[str]:
    """Generate SIF understanding using local LLM."""
    content = read_file(filepath)
    filename = os.path.basename(filepath)
    date = datetime.now(timezone.utc).strftime('%Y-%m-%d')
    
    # Truncate very long files
    if len(content) > 15000:
        # Keep beginning and end
        content = content[:7000] + "\n\n... [TRUNCATED] ...\n\n" + content[-7000:]
    
    prompt_template = DEEP_PROMPT if deep else UNDERSTAND_PROMPT
    prompt = prompt_template.format(
        filename=filename,
        content=content,
        date=date
    )
    
    # Cache key based on content and prompt
    key = hashlib.md5((content + prompt).encode('utf-8')).hexdigest()
    if key in cache:
        return cache[key]
    
    try:
        response = requests.post(
            'http://localhost:11434/api/generate',
            json={
                'model': model,
                'prompt': prompt,
                'stream': False,
                'options': {
                    'temperature': 0.3,
                    'num_predict': 2000
                }
            },
            timeout=120
        )
        result = response.json().get('response', '')
        
        # Extract SIF from response
        sif = extract_sif(result, filename, date)
        
        # Cache the result
        cache[key] = sif
        try:
            with open(cache_file, 'w', encoding='utf-8') as f:
                json.dump(cache, f, indent=2)
        except:
            pass  # Ignore cache write errors
        
        return sif
        
    except Exception as e:
        print(f"  ❌ LLM error: {e}", file=sys.stderr)
        return None


def extract_sif(text: str, filename: str, date: str) -> str:
    """Extract and clean SIF from LLM response."""
    lines = text.strip().split('\n')
    sif_lines = []
    in_sif = False
    
    for line in lines:
        stripped = line.strip()
        
        # Start capturing at @G or N or E lines
        if stripped.startswith('@G '):
            in_sif = True
            sif_lines = [stripped]  # Reset, use this @G
        elif stripped.startswith('```') and in_sif:
            break  # End of code block
        elif in_sif and (stripped.startswith('N ') or stripped.startswith('E ')):
            sif_lines.append(stripped)
        elif stripped.startswith('N ') or stripped.startswith('E '):
            # Found SIF content without @G header
            if not in_sif:
                in_sif = True
                # Add default header
                base = os.path.splitext(filename)[0]
                sif_lines.append(f"@G {base}-understanding opus {date}")
            sif_lines.append(stripped)
    
    if not sif_lines:
        return ""
    
    # Ensure we have a header
    if not sif_lines[0].startswith('@G '):
        base = os.path.splitext(filename)[0]
        sif_lines.insert(0, f"@G {base}-understanding opus {date}")
    
    return '\n'.join(sif_lines)


def store_understanding(agent: str, filepath: str, sif: str) -> bool:
    """Store SIF using remember.py."""
    try:
        result = subprocess.run(
            ["python", "remember.py", agent, filepath, sif],
            capture_output=True,
            text=True,
            cwd=Path(__file__).parent
        )
        return result.returncode == 0
    except Exception as e:
        print(f"  ❌ Store failed: {e}", file=sys.stderr)
        return False


MERGE_PROMPT = '''Here are shallow summaries of files in a codebase. Synthesize into ONE system-level view.

FILES:
{summaries}

Create a CONCISE merged SIF (15-25 nodes max) showing:
1. What the overall system does (1-2 nodes)
2. Major layers/subsystems (3-5 nodes) 
3. How they connect (edges)
4. Key entry points

DO NOT repeat individual file details. Abstract UP.
DO NOT include test files in the architecture.

OUTPUT (SIF only, no explanation):
@G {name}-system opus {date}
N n1 System 'One-line purpose of entire module'
N n2 Layer 'Crypto layer - identity, signing, key derivation'
N n3 Layer 'Storage layer - encrypted memory, semantic search'
N n4 Entry 'Main interface that other code calls'
N n5 Flow 'Data flows from X through Y to Z'
E n2 part_of n1
E n3 part_of n1  
E n4 exposes n1
E n3 depends_on n2'''


def merge_summaries(summaries: list[tuple[str, str]], name: str, model: str) -> Optional[str]:
    """Merge individual file summaries into system-level understanding."""
    date = datetime.now(timezone.utc).strftime('%Y-%m-%d')
    
    # Format summaries for prompt
    summary_text = ""
    for filepath, sif in summaries:
        summary_text += f"\n### {os.path.basename(filepath)}\n{sif}\n"
    
    prompt = MERGE_PROMPT.format(
        summaries=summary_text,
        name=name,
        date=date
    )
    
    try:
        response = requests.post(
            'http://localhost:11434/api/generate',
            json={
                'model': model,
                'prompt': prompt,
                'stream': False,
                'options': {
                    'temperature': 0.3,
                    'num_predict': 2000
                }
            },
            timeout=120
        )
        result = response.json().get('response', '')
        return extract_sif(result, name, date)
    except Exception as e:
        print(f"❌ Merge failed: {e}", file=sys.stderr)
        return None


def main():
    parser = argparse.ArgumentParser(
        description='Instant codebase understanding - parse docstrings into tables',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='''
Examples:
  python shallow_understand.py                      # table of all .py in current dir
  python shallow_understand.py -d enclave/          # table for directory
  python shallow_understand.py --sif *.py           # include SIF output
  python shallow_understand.py --llm *.py           # use LLM for deeper analysis
  python shallow_understand.py -o out.sif *.py      # save SIF to file
'''
    )
    parser.add_argument('files', nargs='*', help='Files to analyze')
    parser.add_argument('-d', '--dir', help='Analyze all .py files in directory')
    parser.add_argument('--sif', action='store_true', help='Also print SIF output (default: table only)')
    parser.add_argument('--llm', action='store_true', help='Use LLM for analysis (slower, deeper)')
    parser.add_argument('--deep', action='store_true', help='Thorough LLM analysis (implies --llm)')
    parser.add_argument('-a', '--agent', help='Store results with remember.py (provide agent id)')
    parser.add_argument('--merge', action='store_true', help='Merge into system-level understanding (implies --llm)')
    parser.add_argument('--name', help='Name for merged graph (default: directory name)')
    parser.add_argument('--model', default='qwen2.5:7b', help='Ollama model (default: qwen2.5:7b)')
    parser.add_argument('-o', '--output', help='Write SIF to file (implies --sif)')
    parser.add_argument('-p', '--parallel', type=int, default=1, help='Parallel workers for LLM mode')
    parser.add_argument('-s', '--stream', action='store_true', help='Stream results as table while processing')
    
    args = parser.parse_args()
    
    # --deep and --merge imply --llm
    use_llm = args.llm or args.deep or args.merge
    
    # Gather files
    files = list(args.files) if args.files else []
    
    if args.dir:
        dir_path = Path(args.dir)
        if dir_path.is_dir():
            files.extend(str(p) for p in dir_path.glob('*.py'))
    
    # Default: current directory if no files specified
    if not files:
        files = [str(p) for p in Path('.').glob('*.py')]
    
    if not files:
        print("No Python files found in current directory.", file=sys.stderr)
        print("Use: python shallow_understand.py file1.py file2.py", file=sys.stderr)
        print("  or: python shallow_understand.py -d directory/", file=sys.stderr)
        sys.exit(1)
    
    all_sif = []
    summaries = []  # For merge mode
    results_for_table = []  # For table.py output
    
    # Import table renderer directly
    sys.path.insert(0, str(Path(__file__).parent))
    try:
        from table import render_table
        has_table = True
    except ImportError:
        has_table = False
    
    # Filter valid files
    valid_files = [f for f in files if os.path.exists(f)]
    for f in files:
        if f not in valid_files:
            print(f"⚠️  Skipping {f}: not found", file=sys.stderr)
    
    # INSTANT MODE (default) - no LLM, just docstrings
    if not use_llm:
        def process_instant(filepath):
            filename = os.path.basename(filepath)
            purpose, funcs = instant_understand(filepath)
            purpose_short = purpose[:55] if len(purpose) > 55 else purpose
            sif = f"@G {filename}-instant opus\nN P '{purpose}'"
            for fn in funcs[:5]:
                sif += f"\nN C '{fn}'"
            return [filename, purpose_short], f"# {filepath}\n{sif}\n", (filepath, sif)
        
        with ThreadPoolExecutor(max_workers=min(len(valid_files), 4)) as executor:
            futures = [executor.submit(process_instant, f) for f in valid_files]
            for future in as_completed(futures):
                row, sif, summary = future.result()
                results_for_table.append(row)
                all_sif.append(sif)
                summaries.append(summary)
        
        # Output as beautiful table
        if has_table:
            print(render_table(["File", "Purpose"], results_for_table), file=sys.stderr)
        else:
            print(f"{'File':<28} {'Purpose':<50}", file=sys.stderr)
            print(f"{'-'*28} {'-'*50}", file=sys.stderr)
            for row in results_for_table:
                print(f"{row[0]:<28} {row[1]:<50}", file=sys.stderr)
        
        print(f"\n✓ {len(valid_files)} files (instant mode)", file=sys.stderr)
    
    else:
        # LLM-based processing
        def extract_purpose(sif: str) -> str:
            """Extract purpose line from SIF for quick display."""
            for line in sif.split('\n'):
                if " Purpose '" in line or " Purpose \"" in line:
                    start = line.find("'") if "'" in line else line.find('"')
                    end = line.rfind("'") if "'" in line else line.rfind('"')
                    if start != -1 and end > start:
                        return line[start+1:end][:60]
            return "(no purpose found)"
        
        def process_file(filepath):
            """Process a single file - for parallel execution."""
            filename = os.path.basename(filepath)
            file_hash = get_file_hash(filepath)
            sif = generate_sif(filepath, args.model, args.deep)
            return filepath, filename, file_hash, sif
        
        # Parallel or sequential processing with streaming output
        if args.parallel > 1:
            print(f"⚡ Processing {len(valid_files)} files with {args.parallel} workers...\n", file=sys.stderr)
            if args.stream:
                # Print header for streaming table
                print(f"{'File':<25} {'Purpose':<55}", file=sys.stderr)
                print(f"{'-'*25} {'-'*55}", file=sys.stderr)
            
            with ThreadPoolExecutor(max_workers=args.parallel) as executor:
                futures = {executor.submit(process_file, f): f for f in valid_files}
                for future in as_completed(futures):
                    filepath, filename, file_hash, sif = future.result()
                    if sif:
                        all_sif.append(f"# {filepath}\n{sif}\n")
                        summaries.append((filepath, sif))
                        if args.stream:
                            purpose = extract_purpose(sif)
                            print(f"{filename:<25} {purpose:<55}", file=sys.stderr)
                        else:
                            print(f"✓ {filename} ({file_hash}) - {len(sif.split(chr(10)))} lines", file=sys.stderr)
                    else:
                        if args.stream:
                            print(f"{filename:<25} {'❌ FAILED':<55}", file=sys.stderr)
                        else:
                            print(f"❌ {filename} failed", file=sys.stderr)
            
            if args.stream:
                print(f"\n✓ Done: {len(summaries)}/{len(valid_files)} files", file=sys.stderr)
        else:
            for filepath in valid_files:
                filename = os.path.basename(filepath)
                file_hash = get_file_hash(filepath)
            print(f"🔍 {filename} ({file_hash})", file=sys.stderr)
            sif = generate_sif(filepath, args.model, args.deep)
            if sif:
                print(f"  ✓ Generated {len(sif.split(chr(10)))} lines", file=sys.stderr)
                all_sif.append(f"# {filepath}\n{sif}\n")
                summaries.append((filepath, sif))
    
    # Store if requested (after parallel processing)
    if args.agent and not args.merge:
        for filepath, sif in summaries:
            if store_understanding(args.agent, filepath, sif):
                print(f"  ✓ Stored {os.path.basename(filepath)} for {args.agent}", file=sys.stderr)
            else:
                print(f"  ⚠️  Store failed for {os.path.basename(filepath)}", file=sys.stderr)
    
    # Merge mode
    if args.merge and summaries:
        print(f"\n🔀 Merging {len(summaries)} summaries...", file=sys.stderr)
        merge_name = args.name or (Path(args.dir).name if args.dir else 'system')
        merged = merge_summaries(summaries, merge_name, args.model)
        if merged:
            print(f"  ✓ System view generated", file=sys.stderr)
            all_sif.append(f"\n# === SYSTEM VIEW ===\n{merged}\n")
    
    # Output SIF only if requested
    if args.output or args.sif:
        output = '\n'.join(all_sif)
        
        if args.output:
            with open(args.output, 'w', encoding='utf-8') as f:
                f.write(output)
            print(f"\n📄 Wrote to {args.output}", file=sys.stderr)
        else:
            print("\n" + "=" * 60)
            print(output)


if __name__ == '__main__':
    main()
