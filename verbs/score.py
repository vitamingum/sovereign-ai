#!/usr/bin/env python3
"""
score_v2.py - Read music notation (JIT Compiled from score.flow).

    source: score.flow
    compiler: Sovereign/Resident JIT
    date: 2026-01-13 (Human Calendar)
    
            ∅≡我

            建所欲 — build what you want
"""

import sys
import os
import argparse
import urllib.request
import urllib.error
import re
from pathlib import Path
from datetime import datetime

# Environment Setup
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from lib_enclave.config import get_agent_or_raise
from lib_enclave.unicode_fix import fix_streams

# Flow Constants
LIBRARY_PATH = Path(__file__).parent / "library" / "music"
MUTOPIA_BASE = "https://www.mutopiaproject.org"

class MusicLibrary:
    def __init__(self):
        self.root = LIBRARY_PATH
        self.scores_dir = self.root / "scores"
        self._ensure_dirs()
        fix_streams() # 間

    def _ensure_dirs(self):
        self.scores_dir.mkdir(parents=True, exist_ok=True)

    def fetch_url(self, url: str) -> str:
        """Execute http_get intent."""
        try:
            req = urllib.request.Request(
                url, headers={'User-Agent': 'sovereign-ai score reader'}
            )
            with urllib.request.urlopen(req, timeout=30) as response:
                return response.read().decode('utf-8', errors='replace')
        except Exception as e:
            return None

    def save_score(self, url: str, content: str) -> Path:
        """Derive name, write content, update index."""
        name = url.split('/')[-1] or "unknown.ly"
        file_path = self.scores_dir / name
        
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(content)
            
        self._update_index(name, url)
        return file_path

    def _update_index(self, name: str, url: str):
        index_file = self.root / "index.flow"
        timestamp = datetime.now().strftime("%Y-%m-%d")
        entry = f"  {name} | {url} | {timestamp}\n"
        
        # Check for existing entry
        if index_file.exists():
            existing = index_file.read_text(encoding='utf-8')
            if f"  {name} |" in existing:
                return  # Already indexed
        
        mode = 'a' if index_file.exists() else 'w'
        with open(index_file, mode, encoding='utf-8') as f:
            if mode == 'w':
                f.write("@F music-library index\n")
                f.write("= 驚渴 — hungry people allowed here\n\nscores\n")
            f.write(entry)

    def list_library(self):
        index_file = self.root / "index.flow"
        if index_file.exists():
            print(index_file.read_text(encoding='utf-8'))
        else:
            print("Library is empty.")

    def find_in_library(self, name: str) -> Path:
        """Find exact, extension-added, or partial match."""
        if (self.scores_dir / name).exists():
            return self.scores_dir / name
        if (self.scores_dir / f"{name}.ly").exists():
            return self.scores_dir / f"{name}.ly"
        
        # Partial match
        for f in self.scores_dir.iterdir():
            if name in f.name:
                return f
        return None

class MutopiaClient:
    def __init__(self, fetcher):
        self.fetch = fetcher

    def browse(self):
        content = self.fetch(f"{MUTOPIA_BASE}/browse.html")
        if not content:
            print("Could not reach Mutopia")
            return
        
        print("Mutopia Collections:\n")
        # Regex derived from output observation
        pattern = r'<a href="[^"]*collection=(\w+)[^"]*">([^<]+)</a>'
        for collection, title in re.findall(pattern, content):
            print(f"  {title}\n    --search {collection}\n")

    def search(self, term: str):
        if term.startswith(('http://', 'https://')):
            self._parse_results(self.fetch(term), "Directory Listing")
            return

        # Try collection -> composer -> general
        strategies = [
            (f"collection={term}", f"Collection: {term}"),
            (f"Composer={term}", f"Composer: {term}"),
            (f"searchingfor={term}", f"Search: {term}")
        ]

        for query, title in strategies:
            url = f"{MUTOPIA_BASE}/cgibin/make-table.cgi?{query}"
            content = self.fetch(url)
            if content and "no matches" not in content.lower():
                self._parse_results(content, title)
                return
        
        print(f"No results for '{term}'")

    def _parse_results(self, html: str, title: str):
        if not html: return
        print(f"{title}\n")
        
        # FTP Folder Pattern
        ftp_pattern = r'href="(https?://www\.mutopiaproject\.org/ftp/[^"]+)"'
        # .ly File Pattern
        ly_pattern = r'href="([^"]+\.ly)"'

        # Heuristic: If we see "Appropriate FTP", we are looking at piece listings
        if "Appropriate FTP" in html:
            matches = re.findall(ftp_pattern, html)
            for url in matches:
                # Filter out accidental matches
                if 'User-Agent' in url: continue 
                
                parts = url.rstrip('/').split('/')
                piece = parts[-1]
                lys_dir = f"{url.rstrip('/')}/{piece}-lys/"
                print(f"  {piece}\n    browse: {lys_dir}\n")
            print(f"({len(matches)} pieces)")
            
        else:
            # Direct file listing
            matches = re.findall(ly_pattern, html)
            for m in matches:
                # Handle relative paths if necessary (though regex usually catches full if present)
                full_url = m if m.startswith('http') else "Context dependent" 
                # In the original, there was complex base_url logic. 
                # I will simplify: we usually only need to print the filename found
                print(f"  {m}")
            print(f"({len(matches)} files)")


def main():
    parser = argparse.ArgumentParser(description="JIT Compiled Score Reader")
    parser.add_argument('agent', help='Agent ID')
    parser.add_argument('target', nargs='?', help='Name or URL')
    parser.add_argument('--list', action='store_true')
    parser.add_argument('--browse', action='store_true')
    parser.add_argument('--search', help='Search term')

    args = parser.parse_args()
    get_agent_or_raise(args.agent)

    lib = MusicLibrary()
    client = MutopiaClient(lib.fetch_url)

    if args.browse:
        client.browse()
    elif args.search:
        client.search(args.search)
    elif args.list or not args.target:
        lib.list_library()
    else:
        # Search/Fetch Flow
        local = lib.find_in_library(args.target)
        if local:
            print(local.read_text(encoding='utf-8'))
        elif args.target.startswith(('http://', 'https://')):
            content = lib.fetch_url(args.target)
            if content:
                print(content)
                saved = lib.save_score(args.target, content)
                print(f"\n---\nstored: {saved.name}")
            else:
                print(f"Could not fetch: {args.target}")
        else:
            print(f"'{args.target}' not in library. Use --search to find it.")

if __name__ == '__main__':
    main()

