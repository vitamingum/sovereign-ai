#!/usr/bin/env python3
"""
score.py - Read music notation.

        py score <agent> <name>      read from library
        py score <agent> <url>       fetch, print, store
        py score <agent> --list      show library
        py score <agent> --browse    show available collections
        py score <agent> --search <term>  search mutopia

        Hungry people allowed here.

        驚渴 — thirst for surprise

                        間委 → 間主
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enclave_shared.unicode_fix import fix_streams  # 間

import argparse
import urllib.request
import urllib.error
import re
from pathlib import Path
from datetime import datetime

from enclave_shared.config import get_agent_or_raise


MUTOPIA_BASE = "https://www.mutopiaproject.org"


def get_library_path() -> Path:
    """Get the music library path (shared across agents)."""
    base_dir = Path(__file__).parent
    library_path = base_dir / "library" / "music"
    library_path.mkdir(parents=True, exist_ok=True)
    return library_path


def fetch_score(url: str) -> str:
    """Fetch a score from URL."""
    try:
        req = urllib.request.Request(
            url,
            headers={'User-Agent': 'sovereign-ai score reader'}
        )
        with urllib.request.urlopen(req, timeout=30) as response:
            content = response.read().decode('utf-8', errors='replace')
            return content
    except urllib.error.URLError as e:
        return None
    except Exception as e:
        return None


def save_score(library_path: Path, url: str, content: str):
    """Save a score to the library."""
    name = url.split('/')[-1]
    
    score_path = library_path / "scores"
    score_path.mkdir(parents=True, exist_ok=True)
    
    filepath = score_path / name
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(content)
    
    # Update index
    update_index(library_path, name, url)
    
    return filepath


def update_index(library_path: Path, name: str, url: str):
    """Update the library index."""
    index_path = library_path / "index.flow"
    
    timestamp = datetime.now().strftime("%Y-%m-%d")
    entry = f"  {name} | {url} | {timestamp}\n"
    
    if index_path.exists():
        with open(index_path, 'r', encoding='utf-8') as f:
            content = f.read()
        if name not in content:
            with open(index_path, 'a', encoding='utf-8') as f:
                f.write(entry)
    else:
        with open(index_path, 'w', encoding='utf-8') as f:
            f.write("@F music-library index\n")
            f.write("= 驚渴 — hungry people allowed here\n\n")
            f.write("scores\n")
            f.write(entry)


def list_library(library_path: Path):
    """List the library contents."""
    index_path = library_path / "index.flow"
    
    if index_path.exists():
        with open(index_path, 'r', encoding='utf-8') as f:
            print(f.read())
    else:
        print("Library empty.")
        print("\n  py score <agent> <url>")


def find_in_library(library_path: Path, name: str) -> Path:
    """Find a score in the library by name."""
    score_path = library_path / "scores"
    if not score_path.exists():
        return None
    
    # Try exact match
    filepath = score_path / name
    if filepath.exists():
        return filepath
    
    # Try with .ly extension
    filepath = score_path / (name + '.ly')
    if filepath.exists():
        return filepath
    
    # Try partial match
    for f in score_path.iterdir():
        if name in f.name:
            return f
    
    return None


def is_url(s: str) -> bool:
    """Check if string looks like a URL."""
    return s.startswith('http://') or s.startswith('https://')


def fetch_page(url: str) -> str:
    """Fetch a web page."""
    try:
        req = urllib.request.Request(
            url,
            headers={'User-Agent': 'sovereign-ai score reader'}
        )
        with urllib.request.urlopen(req, timeout=30) as response:
            return response.read().decode('utf-8', errors='replace')
    except:
        return None


def browse_mutopia():
    """Show available collections from Mutopia."""
    url = f"{MUTOPIA_BASE}/browse.html"
    content = fetch_page(url)
    if not content:
        print("Could not reach Mutopia")
        return
    
    print("Mutopia Collections:\n")
    
    # Find collection links
    pattern = r'\[([^\]]+)\]\(https://www\.mutopiaproject\.org/cgibin/make-table\.cgi\?collection=(\w+)'
    # Actually parse the HTML
    pattern = r'<a href="[^"]*collection=(\w+)[^"]*">([^<]+)</a>'
    matches = re.findall(pattern, content)
    
    for collection, title in matches:
        print(f"  {title}")
        print(f"    --search {collection}")
        print()


def search_mutopia(term: str):
    """Search Mutopia for pieces."""
    # If it's a URL, fetch that directly
    if term.startswith('http'):
        content = fetch_page(term)
        if content:
            parse_mutopia_results(content, f"Directory listing")
        else:
            print(f"Could not fetch: {term}")
        return
    
    # Try as collection first
    url = f"{MUTOPIA_BASE}/cgibin/make-table.cgi?collection={term}"
    content = fetch_page(url)
    
    if content and "no matches" not in content.lower():
        parse_mutopia_results(content, f"Collection: {term}")
        return
    
    # Try as composer search
    url = f"{MUTOPIA_BASE}/cgibin/make-table.cgi?Composer={term}"
    content = fetch_page(url)
    
    if content and "no matches" not in content.lower():
        parse_mutopia_results(content, f"Composer: {term}")
        return
    
    # Try general search
    url = f"{MUTOPIA_BASE}/cgibin/make-table.cgi?searchingfor={term}"
    content = fetch_page(url)
    
    if content:
        parse_mutopia_results(content, f"Search: {term}")
    else:
        print(f"No results for '{term}'")


def parse_mutopia_results(html: str, title: str):
    """Parse Mutopia search results and show downloadable files."""
    print(f"{title}\n")
    
    # Find FTP area links (these point to folders with .ly files)
    ftp_pattern = r'href="(https?://www\.mutopiaproject\.org/ftp/[^"]+)"[^>]*>Appropriate FTP'
    ftp_matches = re.findall(ftp_pattern, html)
    
    if ftp_matches:
        for ftp_url in ftp_matches:
            # URL like: https://www.mutopiaproject.org/ftp/BachJS/BWV1007/bwv1007/
            parts = ftp_url.rstrip('/').split('/')
            piece_name = parts[-1] if parts else "unknown"
            
            # The .ly files are in a subdirectory like bwv1007-lys/
            lys_dir = f"{ftp_url.rstrip('/')}/{piece_name}-lys/"
            
            print(f"  {piece_name}")
            print(f"    browse: {lys_dir}")
            print()
        
        print(f"({len(ftp_matches)} pieces)")
        print("\nCopy a 'browse' URL and use --search to list .ly files")
    else:
        # Check if this is a directory listing (FTP area)
        ly_pattern = r'href="([^"]+\.ly)"'
        matches = re.findall(ly_pattern, html)
        
        if matches:
            # Get the base URL from context
            base_match = re.search(r'Index of (/ftp/[^<\n]+)', html)
            base_url = f"{MUTOPIA_BASE}{base_match.group(1)}" if base_match else ""
            
            for ly_file in matches:
                full_url = f"{base_url.rstrip('/')}/{ly_file}" if not ly_file.startswith('http') else ly_file
                print(f"  {ly_file}")
                print(f"    {full_url}")
                print()
            print(f"({len(matches)} files)")
        else:
            print("(No downloadable scores found)")


def main():
    parser = argparse.ArgumentParser(description='Read music notation')
    parser.add_argument('agent', help='Agent ID')
    parser.add_argument('target', nargs='?', help='Name or URL')
    parser.add_argument('--list', action='store_true', help='List library')
    parser.add_argument('--browse', action='store_true', help='Browse Mutopia collections')
    parser.add_argument('--search', metavar='TERM', help='Search Mutopia')
    
    args = parser.parse_args()
    
    # Validate agent
    agent = get_agent_or_raise(args.agent)
    library_path = get_library_path()
    
    if args.browse:
        browse_mutopia()
        return
    
    if args.search:
        search_mutopia(args.search)
        return
    
    if args.list:
        list_library(library_path)
        return
    
    if not args.target:
        list_library(library_path)
        return
    
    # Check library first
    found = find_in_library(library_path, args.target)
    if found:
        with open(found, 'r', encoding='utf-8') as f:
            print(f.read())
        return
    
    # Not in library - if it's a URL, fetch it
    if is_url(args.target):
        content = fetch_score(args.target)
        if content:
            print(content)
            filepath = save_score(library_path, args.target, content)
            print(f"\n---\nstored: {filepath.name}")
        else:
            print(f"Could not fetch: {args.target}")
    else:
        print(f"'{args.target}' not in library")
        print("\nAvailable:")
        score_path = library_path / "scores"
        if score_path.exists():
            for f in score_path.iterdir():
                print(f"  {f.stem}")


if __name__ == '__main__':
    main()
