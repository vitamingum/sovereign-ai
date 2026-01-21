#!/usr/bin/env python3
"""
read.py - Read books.

    source: data/read.flow
    compiler: gemini
    date: 2026-01-14

        py read <agent> <name>       read from library
        py read <agent> <id>         fetch and store (gutenberg id)
        py read <agent> --list       show library
        py read <agent> --search <term>  search gutenberg
        py read <agent> <name> --chapters      list chapters
        py read <agent> <name> --chapter N     read chapter N

        ∅≡我

        浸 — saturation

                        間委 → 間主
"""

import sys
import os
import argparse
import urllib.request
import urllib.error
import urllib.parse
import re
from pathlib import Path
from datetime import datetime

# Ensure project root in path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from lib_enclave.sovereign_agent import SovereignAgent

GUTENBERG_BASE = "https://www.gutenberg.org"

# Simple regex for chapters
CHAPTER_PATTERN = re.compile(
    r'^(THE\s+)?(Letter|Chapter|CHAPTER|BOOK|Book|PART|Part|ACT|Act|SCENE|Scene|VOLUME|Volume|PROLOGUE|EPILOGUE|Prologue|Epilogue|FIRST|SECOND|THIRD|FOURTH|FIFTH|SIXTH|SEVENTH|EIGHTH|NINTH|TENTH|ELEVENTH|TWELFTH)'
    r'[\s\.:]*'
    r'(BOOK|Book)?'
    r'[\s\.:]*'
    r'([IVXLC]+|\d+)?'
    r'[\s\.\:\]\)]*$'
)

def get_library_path(sov):
    # Using the grid's knowledge of base_dir
    library_path = sov.base_dir / "library" / "books"
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
    start = re.search(r'\*\*\* START OF .+? \*\*\*', content)
    end = re.search(r'\*\*\* END OF .+? \*\*\*', content)
    if start and end:
        return content[start.end():end.start()].strip()
    elif start:
        return content[start.end():].strip()
    return content

def find_chapters(content: str) -> list:
    book_content = extract_book_content(content)
    lines = book_content.split('\n')
    seen = {}
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped and len(stripped) < 60 and CHAPTER_PATTERN.match(stripped):
            seen[stripped] = {'line': i + 1, 'title': stripped}
    return sorted(seen.values(), key=lambda x: x['line'])

def get_chapter(content: str, n: int) -> str:
    chapters = find_chapters(content)
    if n < 1 or n > len(chapters):
        return None
    book_content = extract_book_content(content)
    lines = book_content.split('\n')
    start = chapters[n-1]['line'] - 1
    end = chapters[n]['line'] - 1 if n < len(chapters) else len(lines)
    return '\n'.join(lines[start:end]).strip()

def save_book(library_path: Path, book_id: str, title: str, content: str) -> Path:
    safe_title = re.sub(r'[^\w\s-]', '', title)[:50].strip().replace(' ', '_')
    name = f"{book_id}_{safe_title}.txt"
    texts_path = library_path / "texts"
    texts_path.mkdir(parents=True, exist_ok=True)
    
    filepath = texts_path / name
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(content)
    
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

def get_book_path(library_path: Path, query: str) -> Path:
    texts_path = library_path / "texts"
    if not texts_path.exists(): return None
    
    # Try ID match
    for f in texts_path.glob(f"{query}_*.txt"):
        return f
        
    # Try title match
    files = list(texts_path.glob("*.txt"))
    matches = [f for f in files if query.lower() in f.name.lower()]
    if matches:
        return matches[0]
    return None

def fetch_and_save(sov, book_id: str):
    print(f"Fetching book {book_id}...")
    url = f"{GUTENBERG_BASE}/files/{book_id}/{book_id}-0.txt"
    content = fetch_text(url)
    
    if not content:
        # Try alternate URL pattern
        url = f"{GUTENBERG_BASE}/cache/epub/{book_id}/pg{book_id}.txt"
        content = fetch_text(url)
    
    if not content:
        print("Failed to fetch.")
        return
        
    # Parse title
    title_match = re.search(r"Title:\s+(.+)", content)
    title = title_match.group(1).strip() if title_match else "Unknown Title"
    
    lib_path = get_library_path(sov)
    filepath = save_book(lib_path, book_id, title, content)
    print(f"Saved: {title} ({filepath})")

def main():
    parser = argparse.ArgumentParser(description="Sovereign AI Reader (Grid Enabled)")
    parser.add_argument("agent", help="Agent ID")
    parser.add_argument("query", nargs="?", help="Book ID or name")
    parser.add_argument("--list", action="store_true", help="List saved books")
    parser.add_argument("--search", help="Search Gutenberg (not implemented locally)")
    parser.add_argument("--chapters", action="store_true", help="List chapters")
    parser.add_argument("--chapter", type=int, help="Read specific chapter")
    
    args = parser.parse_args()
    
    # Grid Init
    sov = SovereignAgent.from_id(args.agent) # Handles unicode fix + auth (though read doesn't strictly need auth for files)
    
    lib_path = get_library_path(sov)

    if args.list:
        index_path = lib_path / "index.flow"
        if index_path.exists():
            print(index_path.read_text(encoding='utf-8'))
        else:
            print("(Library empty)")
        return

    if not args.query:
        print("Usage: py read <agent> <book_id|name>")
        return

    # Check if download requested (numeric ID)
    if args.query.isdigit() and not get_book_path(lib_path, args.query):
        fetch_and_save(sov, args.query)
        return

    # Read from library
    filepath = get_book_path(lib_path, args.query)
    if not filepath:
        # If numeric, maybe download?
        if args.query.isdigit():
             fetch_and_save(sov, args.query)
             filepath = get_book_path(lib_path, args.query)
             if not filepath: return
        else:
             print("Book not found in library.")
             return
             
    content = filepath.read_text(encoding='utf-8')
    
    if args.chapters:
        chapters = find_chapters(content)
        if not chapters:
            print("No chapters found.")
        else:
            print("浸\n")
            for i, ch in enumerate(chapters, 1):
                print(f"  {i:3}  {ch['title']}")
        return
        
    if args.chapter:
        text = get_chapter(content, args.chapter)
        if text:
            print(text)
        else:
            print("Chapter not found.")
        return
        
    # Default: Dump content (or extract inner book content)
    print(extract_book_content(content))

if __name__ == "__main__":
    main()

