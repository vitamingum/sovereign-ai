#!/usr/bin/env python3
"""
read.py - Read books.

        py read <agent> <name>       read from library
        py read <agent> <id>         fetch, print, store (gutenberg id)
        py read <agent> --list       show library
        py read <agent> --search <term>  search gutenberg

        浸 — to soak, immerse

                        間委 → 間主
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enclave_shared.unicode_fix import fix_streams  # 間

import argparse
import urllib.request
import urllib.error
import urllib.parse
import re
from pathlib import Path
from datetime import datetime

from enclave_shared.config import get_agent_or_raise


GUTENBERG_BASE = "https://www.gutenberg.org"


def get_library_path() -> Path:
    """Get the book library path (shared across agents)."""
    base_dir = Path(__file__).parent
    library_path = base_dir / "library" / "books"
    library_path.mkdir(parents=True, exist_ok=True)
    return library_path


def fetch_text(url: str) -> str:
    """Fetch text from URL."""
    try:
        req = urllib.request.Request(
            url,
            headers={'User-Agent': 'sovereign-ai book reader'}
        )
        with urllib.request.urlopen(req, timeout=60) as response:
            content = response.read().decode('utf-8', errors='replace')
            return content
    except urllib.error.URLError as e:
        return None
    except Exception as e:
        return None


def save_book(library_path: Path, book_id: str, title: str, content: str):
    """Save a book to the library."""
    # Clean title for filename
    safe_title = re.sub(r'[^\w\s-]', '', title)[:50].strip().replace(' ', '_')
    name = f"{book_id}_{safe_title}.txt"
    
    books_path = library_path / "texts"
    books_path.mkdir(parents=True, exist_ok=True)
    
    filepath = books_path / name
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(content)
    
    # Update index
    update_index(library_path, book_id, title)
    
    return filepath


def update_index(library_path: Path, book_id: str, title: str):
    """Update the library index."""
    index_path = library_path / "index.flow"
    
    timestamp = datetime.now().strftime("%Y-%m-%d")
    entry = f"  {book_id} | {title} | {timestamp}\n"
    
    if index_path.exists():
        with open(index_path, 'r', encoding='utf-8') as f:
            content = f.read()
        if f"| {title} |" not in content:
            with open(index_path, 'a', encoding='utf-8') as f:
                f.write(entry)
    else:
        with open(index_path, 'w', encoding='utf-8') as f:
            f.write("@F book-library index\n")
            f.write("= 浸 — saturation\n\n")
            f.write("books\n")
            f.write(entry)


def list_library(library_path: Path):
    """List the library contents."""
    index_path = library_path / "index.flow"
    
    if index_path.exists():
        with open(index_path, 'r', encoding='utf-8') as f:
            print(f.read())
    else:
        print("Library empty.")
        print("\n  py read <agent> <id>     (gutenberg ebook id)")
        print("  py read <agent> --search <term>")


def find_in_library(library_path: Path, term: str) -> Path:
    """Find a book in the library by id or name."""
    books_path = library_path / "texts"
    if not books_path.exists():
        return None
    
    # Try by id prefix
    for f in books_path.iterdir():
        if f.name.startswith(f"{term}_"):
            return f
    
    # Try partial match on filename
    term_lower = term.lower()
    for f in books_path.iterdir():
        if term_lower in f.name.lower():
            return f
    
    return None


def is_gutenberg_id(s: str) -> bool:
    """Check if string looks like a Gutenberg ebook ID."""
    return s.isdigit()


def get_gutenberg_text_url(book_id: str) -> str:
    """Get the plain text URL for a Gutenberg book."""
    return f"https://www.gutenberg.org/cache/epub/{book_id}/pg{book_id}.txt"


def get_gutenberg_page_url(book_id: str) -> str:
    """Get the ebook page URL."""
    return f"https://www.gutenberg.org/ebooks/{book_id}"


def extract_title(content: str) -> str:
    """Extract book title from Gutenberg text."""
    # Look for Title: line in header
    match = re.search(r'^Title:\s*(.+)$', content, re.MULTILINE)
    if match:
        return match.group(1).strip()
    return "Unknown"


def search_gutenberg(term: str):
    """Search Gutenberg for books."""
    # URL encode the search term
    encoded = urllib.parse.quote(term)
    url = f"{GUTENBERG_BASE}/ebooks/search/?query={encoded}&submit_search=Go%21"
    
    content = fetch_text(url)
    if not content:
        print(f"Could not search Gutenberg")
        return
    
    print(f"Search: {term}\n")
    
    # Parse results - look for ebook links
    # Links like: <a href="/ebooks/84">...</a>
    # Find all links and their text
    pattern = r'<a[^>]*href="/ebooks/(\d+)"[^>]*>([^<]*(?:<[^/][^>]*>[^<]*</[^>]*>)*[^<]*)</a>'
    matches = re.findall(pattern, content)
    
    if not matches:
        # Simpler pattern
        pattern = r'href="/ebooks/(\d+)"'
        ids = re.findall(pattern, content)
        if ids:
            seen = set()
            for book_id in ids[:15]:
                if book_id not in seen:
                    seen.add(book_id)
                    print(f"  {book_id}")
            print(f"\n({len(seen)} books found)")
            print("\nUse ID to fetch and see title:")
            print("  py read <agent> <id>")
            return
    
    if matches:
        seen = set()
        for book_id, title in matches[:20]:
            # Clean up title (remove HTML tags)
            title = re.sub(r'<[^>]+>', ' ', title)
            title = ' '.join(title.split())[:60]
            if book_id not in seen and title:
                seen.add(book_id)
                print(f"  {book_id}: {title}")
        print(f"\n({len(seen)} results)")
        print("\nUse the ID to fetch:")
        print("  py read <agent> <id>")
    else:
        print("No results found")


def main():
    parser = argparse.ArgumentParser(description='Read books')
    parser.add_argument('agent', help='Agent ID')
    parser.add_argument('target', nargs='?', help='Name, ID, or search term')
    parser.add_argument('--list', action='store_true', help='List library')
    parser.add_argument('--search', metavar='TERM', help='Search Gutenberg')
    
    args = parser.parse_args()
    
    # Validate agent
    agent = get_agent_or_raise(args.agent)
    library_path = get_library_path()
    
    if args.search:
        search_gutenberg(args.search)
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
    
    # Not in library - if it's a Gutenberg ID, fetch it
    if is_gutenberg_id(args.target):
        url = get_gutenberg_text_url(args.target)
        print(f"Fetching {url}...")
        content = fetch_text(url)
        if content:
            title = extract_title(content)
            print(f"\n{title}\n")
            print(content)
            filepath = save_book(library_path, args.target, title, content)
            print(f"\n---\nstored: {filepath.name}")
        else:
            print(f"Could not fetch book {args.target}")
            print(f"Check: {get_gutenberg_page_url(args.target)}")
    else:
        print(f"'{args.target}' not in library")
        print("\nTry:")
        print(f"  py read {args.agent} --search {args.target}")


if __name__ == '__main__':
    main()
