#!/usr/bin/env python3
"""
chat_search.py - Search indexed chat history

Usage:
    py chat_search.py "chat indexing"     # Find where we discussed chat indexing
    py chat_search.py "theme vs topic"    # Find that naming discussion
    py chat_search.py -n 5 "encryption"   # Last 5 matches

Fast FTS5 search across 4200+ indexed requests.
"""

import sqlite3
import argparse
from pathlib import Path
from datetime import datetime

INDEX_DB = Path(__file__).parent / "enclave" / "chat_index.db"


def search(query: str, limit: int = 3, context_chars: int = 300) -> list[dict]:
    """Search chat history, return most relevant recent matches."""
    if not INDEX_DB.exists():
        return []
    
    conn = sqlite3.connect(INDEX_DB)
    conn.row_factory = sqlite3.Row
    
    # FTS5 match with snippet extraction
    rows = conn.execute("""
        SELECT 
            r.session_id,
            r.timestamp,
            r.model_id,
            r.user_text,
            r.response_text,
            s.title
        FROM requests r
        JOIN sessions s ON r.session_id = s.session_id
        WHERE r.request_id IN (
            SELECT request_id FROM requests 
            WHERE user_text LIKE ? OR response_text LIKE ?
        )
        ORDER BY r.timestamp DESC
        LIMIT ?
    """, (f'%{query}%', f'%{query}%', limit * 3)).fetchall()
    
    conn.close()
    
    results = []
    seen_content = set()
    
    for row in rows:
        user = row['user_text'] or ''
        response = row['response_text'] or ''
        
        # Find the match context
        query_lower = query.lower()
        
        # Check which field has the match and extract context
        context = None
        if query_lower in user.lower():
            idx = user.lower().find(query_lower)
            start = max(0, idx - 100)
            end = min(len(user), idx + len(query) + context_chars)
            context = ('user', user[start:end].strip())
        elif query_lower in response.lower():
            idx = response.lower().find(query_lower)
            start = max(0, idx - 100)
            end = min(len(response), idx + len(query) + context_chars)
            context = ('assistant', response[start:end].strip())
        
        if not context:
            continue
            
        # Dedupe similar content
        content_key = context[1][:100]
        if content_key in seen_content:
            continue
        seen_content.add(content_key)
        
        ts = datetime.fromtimestamp(row['timestamp']/1000) if row['timestamp'] else None
        
        results.append({
            'timestamp': ts,
            'model': row['model_id'].replace('copilot/', '') if row['model_id'] else 'unknown',
            'title': row['title'],
            'match_in': context[0],
            'context': context[1],
            'user_preview': user[:150] if user else '',
        })
        
        if len(results) >= limit:
            break
    
    return results


def format_results(results: list[dict], query: str) -> str:
    """Format search results for display."""
    if not results:
        return f"No matches for '{query}'"
    
    lines = [f"=== Chat search: '{query}' ({len(results)} matches) ===\n"]
    
    for r in results:
        ts = r['timestamp'].strftime("%Y-%m-%d %H:%M") if r['timestamp'] else "unknown"
        lines.append(f"[{ts}] {r['model']} | {r['title'][:50]}")
        
        # Show context with match highlighted conceptually
        ctx = r['context'].replace('\n', ' ')
        if len(ctx) > 400:
            ctx = ctx[:400] + "..."
        
        lines.append(f"  {r['match_in'].upper()}: {ctx}")
        lines.append("")
    
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description="Search chat history")
    parser.add_argument('query', help='Search term')
    parser.add_argument('-n', '--limit', type=int, default=3, help='Max results')
    parser.add_argument('--json', action='store_true', help='Output as JSON')
    
    args = parser.parse_args()
    
    results = search(args.query, limit=args.limit)
    
    if args.json:
        import json
        print(json.dumps(results, default=str, indent=2))
    else:
        print(format_results(results, args.query))


if __name__ == "__main__":
    main()
