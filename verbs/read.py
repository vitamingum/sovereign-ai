#!/usr/bin/env python3
"""
read.py - Read books from the library.

    py read <agent> <query>              orient (first touch)
    py read <agent> <query> 2            page 2
    py read <agent> <query> --wander     驚渴 random passage
    py read <agent> <query> --grep <pat>  find pattern in book
    py read <agent> --list               show library
    py read <agent> --search <term>      search gutenberg

    浸 — saturation
    
    the distinction between local and remote is invisible
    structure is earned, not assumed
"""

import sys
import os
import argparse
import urllib.request
import urllib.error
import urllib.parse
import re
import random
from pathlib import Path
from datetime import datetime

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from lib_enclave.sovereign_agent import SovereignAgent

GUTENBERG_BASE = "https://www.gutenberg.org"
LINES_PER_PAGE = 60

def get_library_path(sov):
    library_path = sov.base_dir / "library" / "books"
    library_path.mkdir(parents=True, exist_ok=True)
    return library_path

def search_gutenberg(query: str, max_results: int = 20) -> list:
    """Search Project Gutenberg catalog."""
    search_url = f"https://gutendex.com/books/?search={urllib.parse.quote(query)}"
    try:
        req = urllib.request.Request(search_url, headers={'User-Agent': 'sovereign-ai'})
        with urllib.request.urlopen(req, timeout=30) as response:
            import json
            data = json.loads(response.read().decode('utf-8'))
            results = []
            for book in data.get('results', [])[:max_results]:
                authors = ', '.join(a.get('name', 'Unknown') for a in book.get('authors', []))
                results.append({
                    'id': book.get('id'),
                    'title': book.get('title', 'Unknown'),
                    'authors': authors,
                    'languages': book.get('languages', []),
                })
            return results
    except Exception as e:
        print(f"Search failed: {e}")
        return []

def fetch_text(url: str) -> str:
    try:
        req = urllib.request.Request(url, headers={'User-Agent': 'sovereign-ai'})
        with urllib.request.urlopen(req, timeout=60) as response:
            return response.read().decode('utf-8', errors='replace')
    except:
        return None

def extract_book_content(content: str) -> str:
    """Strip Gutenberg header/footer."""
    start = re.search(r'\*\*\* START OF .+? \*\*\*', content)
    end = re.search(r'\*\*\* END OF .+? \*\*\*', content)
    if start and end:
        return content[start.end():end.start()].strip()
    elif start:
        return content[start.end():].strip()
    return content

def get_metadata(content: str) -> dict:
    """Extract title and author from Gutenberg header."""
    title_match = re.search(r"Title:\s+(.+)", content)
    author_match = re.search(r"Author:\s+(.+)", content)
    return {
        'title': title_match.group(1).strip() if title_match else "Unknown",
        'author': author_match.group(1).strip() if author_match else "Unknown",
    }

def save_book(library_path: Path, book_id: str, title: str, content: str) -> Path:
    safe_title = re.sub(r'[^\w\s-]', '', title)[:50].strip().replace(' ', '_')
    name = f"{book_id}_{safe_title}.txt"
    texts_path = library_path / "texts"
    texts_path.mkdir(parents=True, exist_ok=True)
    
    filepath = texts_path / name
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(content)
    
    return filepath

def get_book_path(library_path: Path, query: str) -> Path:
    texts_path = library_path / "texts"
    if not texts_path.exists(): return None
    
    for f in texts_path.glob(f"{query}_*.txt"):
        return f
        
    files = list(texts_path.glob("*.txt"))
    matches = [f for f in files if query.lower() in f.name.lower()]
    if matches:
        return matches[0]
    return None

def fetch_and_save(sov, book_id: str) -> Path:
    """Download book, save, return path."""
    print(f"Fetching {book_id}...")
    url = f"{GUTENBERG_BASE}/files/{book_id}/{book_id}-0.txt"
    content = fetch_text(url)
    
    if not content:
        url = f"{GUTENBERG_BASE}/cache/epub/{book_id}/pg{book_id}.txt"
        content = fetch_text(url)
    
    if not content:
        print("Failed to fetch.")
        return None
        
    meta = get_metadata(content)
    lib_path = get_library_path(sov)
    filepath = save_book(lib_path, book_id, meta['title'], content)
    return filepath

def orient(filepath: Path):
    """First touch: metadata + opening + invitation."""
    content = filepath.read_text(encoding='utf-8')
    meta = get_metadata(content)
    book = extract_book_content(content)
    lines = book.split('\n')
    total_lines = len(lines)
    total_pages = (total_lines // LINES_PER_PAGE) + 1
    
    # Opening: first 12 non-empty lines
    opening = []
    for line in lines:
        if line.strip():
            opening.append(line)
            if len(opening) >= 12:
                break
    
    print(f"{meta['title']}")
    print(f"{meta['author']}")
    print(f"~{total_lines:,} lines ({total_pages} pages)\n")
    print("---")
    for line in opening:
        print(line)
    print("---\n")
    print(f"  py read <agent> {filepath.stem.split('_')[0]} 1      → page 1")
    print(f"  py read <agent> {filepath.stem.split('_')[0]} --wander   → random passage")

def show_page(filepath: Path, page: int):
    """Show a specific page."""
    content = filepath.read_text(encoding='utf-8')
    book = extract_book_content(content)
    lines = book.split('\n')
    total_lines = len(lines)
    total_pages = (total_lines // LINES_PER_PAGE) + 1
    
    if page < 1 or page > total_pages:
        print(f"Page {page} out of range (1-{total_pages})")
        return
    
    start = (page - 1) * LINES_PER_PAGE
    end = start + LINES_PER_PAGE
    page_lines = lines[start:end]
    
    meta = get_metadata(content)
    print(f"{meta['title']} — page {page}/{total_pages}\n")
    print('\n'.join(page_lines))
    
    if page < total_pages:
        print(f"\n  → {page + 1}  next page")

def wander(filepath: Path):
    """驚渴 — random passage."""
    content = filepath.read_text(encoding='utf-8')
    book = extract_book_content(content)
    lines = book.split('\n')
    
    if len(lines) < 40:
        start = 0
    else:
        start = random.randint(0, len(lines) - 35)
    
    passage = lines[start:start + 30]
    
    meta = get_metadata(content)
    print(f"{meta['title']} — 驚渴\n")
    print("---")
    for line in passage:
        print(line)
    print("---\n")
    print(f"  --wander  again")

def grep(filepath: Path, pattern: str):
    """Find pattern in book, show in context."""
    content = filepath.read_text(encoding='utf-8')
    book = extract_book_content(content)
    lines = book.split('\n')
    meta = get_metadata(content)
    
    hits = []
    for i, line in enumerate(lines):
        if re.search(pattern, line, re.IGNORECASE):
            hits.append(i)
    
    if not hits:
        print(f"No matches for '{pattern}'")
        return
    
    print(f"{meta['title']} — {len(hits)} matches for '{pattern}'\n")
    
    shown = set()
    for i in hits[:10]:  # max 10 matches
        start = max(0, i - 2)
        end = min(len(lines), i + 3)
        if start in shown:
            continue
        shown.add(start)
        print(f"[{i + 1}]")
        for j in range(start, end):
            marker = "→" if j == i else " "
            print(f"{marker} {lines[j]}")
        print()

def main():
    parser = argparse.ArgumentParser(description="Read books")
    parser.add_argument("agent", help="Agent ID")
    parser.add_argument("query", nargs="?", help="Book ID, name, or search term")
    parser.add_argument("page", nargs="?", type=int, help="Page number")
    parser.add_argument("--list", action="store_true", help="List library")
    parser.add_argument("--search", help="Search Gutenberg")
    parser.add_argument("--wander", action="store_true", help="Random passage")
    parser.add_argument("--grep", help="Find pattern in book")
    
    args = parser.parse_args()
    
    sov = SovereignAgent.from_id(args.agent)
    lib_path = get_library_path(sov)

    # --list
    if args.list:
        index_path = lib_path / "index.flow"
        if index_path.exists():
            print(index_path.read_text(encoding='utf-8'))
        else:
            print("(Library empty)")
        print("\n  --search <term>  to find more")
        return

    # --search
    if args.search:
        print(f"Searching: {args.search}\n")
        results = search_gutenberg(args.search)
        if not results:
            print("No results.")
        else:
            print("浸\n")
            for r in results:
                langs = ','.join(r['languages'])
                print(f"  {r['id']:6}  {r['title'][:50]:<50}  {r['authors'][:25]}")
            print(f"\n  py read <agent> <id>  to read")
        return

    if not args.query:
        print("Usage: py read <agent> <query> [page]")
        print("       py read <agent> --list")
        print("       py read <agent> --search <term>")
        return

    # Find or fetch book
    filepath = get_book_path(lib_path, args.query)
    
    if not filepath:
        if args.query.isdigit():
            # Numeric ID — fetch it
            filepath = fetch_and_save(sov, args.query)
            if not filepath:
                return
        else:
            # Not found — search
            print(f"Not in library. Searching '{args.query}'...\n")
            results = search_gutenberg(args.query)
            if results:
                print("浸 — found:\n")
                for r in results[:5]:
                    print(f"  {r['id']:6}  {r['title'][:60]}")
                print(f"\n  py read <agent> <id>  to read")
            else:
                print("Not found.")
            return

    # Have filepath — what to do with it?
    if args.grep:
        grep(filepath, args.grep)
    elif args.wander:
        wander(filepath)
    elif args.page:
        show_page(filepath, args.page)
    else:
        orient(filepath)

if __name__ == "__main__":
    main()

