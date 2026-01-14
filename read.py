#!/usr/bin/env python3
"""
read.py - Read books.

        py read <agent> <name>       read from library
        py read <agent> <id>         fetch and store (gutenberg id)
        py read <agent> --list       show library
        py read <agent> --search <term>  search gutenberg
        py read <agent> <name> --chapters      list chapters
        py read <agent> <name> --chapter N     read chapter N

        浸 — saturation — room to dwell

                        間委 → 間主
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enclave_shared.unicode_fix import fix_streams

import argparse
import urllib.request
import urllib.error
import urllib.parse
import re
from pathlib import Path
from datetime import datetime

from enclave_shared.config import get_agent_or_raise


GUTENBERG_BASE = "https://www.gutenberg.org"

# Broad pattern - catches most chapter formats
# Must start with capital letter and be a standalone heading
CHAPTER_PATTERN = re.compile(
    r'^(THE\s+)?(Letter|Chapter|CHAPTER|BOOK|Book|PART|Part|ACT|Act|SCENE|Scene|VOLUME|Volume|PROLOGUE|EPILOGUE|Prologue|Epilogue|FIRST|SECOND|THIRD|FOURTH|FIFTH|SIXTH|SEVENTH|EIGHTH|NINTH|TENTH|ELEVENTH|TWELFTH)'
    r'[\s\.:]*'
    r'(BOOK|Book)?'
    r'[\s\.:]*'
    r'([IVXLC]+|\d+)?'
    r'[\s\.\:\]\)]*$'
)


def get_library_path() -> Path:
    base_dir = Path(__file__).parent
    library_path = base_dir / "library" / "books"
    library_path.mkdir(parents=True, exist_ok=True)
    return library_path


def fetch_text(url: str) -> str:
    try:
        req = urllib.request.Request(url, headers={'User-Agent': 'sovereign-ai'})
        with urllib.request.urlopen(req, timeout=60) as response:
            return response.read().decode('utf-8', errors='replace')
    except:
        return None


def extract_book_content(content: str) -> str:
    """Extract content between Gutenberg markers."""
    start = re.search(r'\*\*\* START OF .+? \*\*\*', content)
    end = re.search(r'\*\*\* END OF .+? \*\*\*', content)
    if start and end:
        return content[start.end():end.start()].strip()
    elif start:
        return content[start.end():].strip()
    return content


def find_chapters(content: str) -> list:
    """Find chapters, keeping last occurrence of each (skips TOC)."""
    book_content = extract_book_content(content)
    lines = book_content.split('\n')
    
    # Find all matching lines
    seen = {}
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped and len(stripped) < 60 and CHAPTER_PATTERN.match(stripped):
            seen[stripped] = {'line': i + 1, 'title': stripped}
    
    # Sort by line number
    return sorted(seen.values(), key=lambda x: x['line'])


def get_chapter(content: str, n: int) -> str:
    """Get chapter N (1-indexed)."""
    chapters = find_chapters(content)
    if n < 1 or n > len(chapters):
        return None
    
    book_content = extract_book_content(content)
    lines = book_content.split('\n')
    
    start = chapters[n-1]['line'] - 1
    end = chapters[n]['line'] - 1 if n < len(chapters) else len(lines)
    
    return '\n'.join(lines[start:end]).strip()


def list_chapters(content: str):
    chapters = find_chapters(content)
    if not chapters:
        print("No chapters found.")
        return
    
    print("浸\n")
    for i, ch in enumerate(chapters, 1):
        print(f"  {i:3}  {ch['title']}")
    print(f"\n({len(chapters)} chapters)")


# --- Library functions ---

def save_book(library_path: Path, book_id: str, title: str, content: str) -> Path:
    safe_title = re.sub(r'[^\w\s-]', '', title)[:50].strip().replace(' ', '_')
    name = f"{book_id}_{safe_title}.txt"
    
    texts_path = library_path / "texts"
    texts_path.mkdir(parents=True, exist_ok=True)
    
    filepath = texts_path / name
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(content)
    
    # Update index
    index_path = library_path / "index.flow"
    timestamp = datetime.now().strftime("%Y-%m-%d")
    entry = f"  {book_id} | {title} | {timestamp}\n"
    
    if index_path.exists():
        existing = index_path.read_text(encoding='utf-8')
        if f"| {title} |" not in existing:
            with open(index_path, 'a', encoding='utf-8') as f:
                f.write(entry)
    else:
        with open(index_path, 'w', encoding='utf-8') as f:
            f.write("@F book-library index\n= 浸 — saturation\n\nbooks\n")
            f.write(entry)
    
    return filepath


def list_library(library_path: Path):
    index_path = library_path / "index.flow"
    if index_path.exists():
        print(index_path.read_text(encoding='utf-8'))
    else:
        print("Library empty.\n")
        print("  py read <agent> <id>     (gutenberg ebook id)")
        print("  py read <agent> --search <term>")


def find_in_library(library_path: Path, term: str) -> Path:
    texts_path = library_path / "texts"
    if not texts_path.exists():
        return None
    
    term_lower = term.lower()
    for f in texts_path.iterdir():
        if f.suffix == '.txt':
            if f.name.startswith(f"{term}_") or term_lower in f.name.lower():
                return f
    return None


def extract_title(content: str) -> str:
    match = re.search(r'^Title:\s*(.+)$', content, re.MULTILINE)
    return match.group(1).strip() if match else "Unknown"


def search_gutenberg(term: str):
    encoded = urllib.parse.quote(term)
    url = f"{GUTENBERG_BASE}/ebooks/search/?query={encoded}&submit_search=Go%21"
    
    content = fetch_text(url)
    if not content:
        print("Could not search Gutenberg")
        return
    
    print(f"Search: {term}\n")
    
    pattern = r'href="/ebooks/(\d+)"'
    ids = re.findall(pattern, content)
    
    seen = set()
    for book_id in ids[:15]:
        if book_id not in seen:
            seen.add(book_id)
            print(f"  {book_id}")
    
    if seen:
        print(f"\n({len(seen)} results)")
        print("\n  py read <agent> <id>")


# --- Main ---

def main():
    parser = argparse.ArgumentParser(description='Read books')
    parser.add_argument('agent', help='Agent ID')
    parser.add_argument('target', nargs='?', help='Name or Gutenberg ID')
    parser.add_argument('--list', action='store_true', help='List library')
    parser.add_argument('--search', metavar='TERM', help='Search Gutenberg')
    parser.add_argument('--chapters', action='store_true', help='List chapters')
    parser.add_argument('--chapter', type=int, metavar='N', help='Read chapter N')
    
    args = parser.parse_args()
    
    agent = get_agent_or_raise(args.agent)
    library_path = get_library_path()
    
    if args.search:
        search_gutenberg(args.search)
        return
    
    if args.list or not args.target:
        list_library(library_path)
        return
    
    # Check library
    found = find_in_library(library_path, args.target)
    if found:
        content = found.read_text(encoding='utf-8')
        
        if args.chapters:
            list_chapters(content)
        elif args.chapter:
            text = get_chapter(content, args.chapter)
            if text:
                print(text)
            else:
                print(f"Chapter {args.chapter} not found.")
        else:
            print(content)
        return
    
    # Fetch from Gutenberg
    if args.target.isdigit():
        url = f"https://www.gutenberg.org/cache/epub/{args.target}/pg{args.target}.txt"
        print(f"Fetching...")
        content = fetch_text(url)
        if content:
            title = extract_title(content)
            filepath = save_book(library_path, args.target, title, content)
            print(f"Stored: {title}\n")
            
            if args.chapters:
                list_chapters(content)
            elif args.chapter:
                text = get_chapter(content, args.chapter)
                if text:
                    print(text)
            else:
                print(content)
        else:
            print(f"Could not fetch book {args.target}")
    else:
        print(f"'{args.target}' not in library")
        print(f"\n  py read {args.agent} --search {args.target}")


if __name__ == '__main__':
    main()
