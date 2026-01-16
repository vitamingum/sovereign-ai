#!/usr/bin/env python3
"""Bulk import .sif files as themes into semantic memory."""
import subprocess
import sys
from pathlib import Path
import re

def extract_theme_from_sif(filepath):
    """Extract theme name from @G header."""
    try:
        with open(filepath, 'r') as f:
            first_line = f.readline().strip()
        
        # Skip comments
        if first_line.startswith('#'):
            return None
            
        # Parse @G header: @G <theme-id> [creator] [date]
        match = re.match(r'@G\s+(\S+)', first_line)
        if match:
            return match.group(1)
    except Exception as e:
        print(f"  Error reading {filepath}: {e}")
    return None

def import_sif(agent, theme, filepath):
    """Import a .sif file as a theme."""
    cmd = [sys.executable, 'remember.py', agent, '--theme', theme, f'@{filepath}']
    result = subprocess.run(cmd, capture_output=True, text=True)
    return result.returncode == 0, result.stdout + result.stderr

def main():
    agent = sys.argv[1] if len(sys.argv) > 1 else 'opus'
    
    # Find all .sif files
    sif_files = list(Path('.').rglob('*.sif'))
    
    # Skip templates and test files
    skip_patterns = ['templates/', 'test_', 'test-', '_temp', 'handoff_forge']
    
    imported = []
    skipped = []
    failed = []
    
    for sif_path in sorted(sif_files):
        path_str = str(sif_path)
        
        # Skip certain patterns
        if any(p in path_str for p in skip_patterns):
            skipped.append((path_str, "matches skip pattern"))
            continue
            
        theme = extract_theme_from_sif(sif_path)
        if not theme:
            skipped.append((path_str, "no @G header"))
            continue
            
        # Skip placeholder themes
        if '<' in theme or '>' in theme:
            skipped.append((path_str, f"placeholder theme: {theme}"))
            continue
        
        print(f"Importing {path_str} as theme '{theme}'...")
        success, output = import_sif(agent, theme, path_str)
        
        if success and "Remembered" in output:
            imported.append((path_str, theme))
            print(f"  ✅ {theme}")
        else:
            failed.append((path_str, theme, output.strip()))
            print(f"  ❌ {theme}: {output.strip()[:100]}")
    
    print(f"\n=== SUMMARY ===")
    print(f"Imported: {len(imported)}")
    print(f"Skipped:  {len(skipped)}")
    print(f"Failed:   {len(failed)}")
    
    if failed:
        print("\nFailed imports:")
        for path, theme, err in failed:
            print(f"  {path} ({theme}): {err[:80]}")

if __name__ == '__main__':
    main()
