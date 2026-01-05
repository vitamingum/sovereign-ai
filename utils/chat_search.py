#!/usr/bin/env python3
"""
chat_search.py - Search VS Code chat history with auto-indexing

Usage:
    py chat_search.py "chat indexing"     # Find where we discussed chat indexing
    py chat_search.py "theme vs topic"    # Find that naming discussion
    py chat_search.py -n 5 "encryption"   # Last 5 matches
    py chat_search.py --stats             # Show index statistics
    py chat_search.py --export opus       # Export opus chats to JSONL
    py chat_search.py --reindex           # Force full re-index

Auto-indexes on every search (instant if no changes due to mtime check).
FTS5 search across 4500+ indexed requests.
"""

import sqlite3
import json
from pathlib import Path
from datetime import datetime

WORKSPACE_STORAGE = Path.home() / "AppData/Roaming/Code/User/workspaceStorage"
INDEX_DB = Path(__file__).parent / "enclave" / "chat_index.db"


# ═══════════════════════════════════════════════════════════════════════════════
# INDEXING
# ═══════════════════════════════════════════════════════════════════════════════

def init_index_db():
    """Create index database schema."""
    INDEX_DB.parent.mkdir(exist_ok=True)
    conn = sqlite3.connect(INDEX_DB)
    conn.executescript("""
        CREATE TABLE IF NOT EXISTS workspaces (
            ws_hash TEXT PRIMARY KEY,
            path TEXT
        );
        
        CREATE TABLE IF NOT EXISTS sessions (
            session_id TEXT PRIMARY KEY,
            ws_hash TEXT,
            title TEXT,
            created_at INTEGER,
            last_msg_at INTEGER,
            request_count INTEGER,
            models TEXT,
            size_kb REAL,
            file_mtime REAL,
            FOREIGN KEY (ws_hash) REFERENCES workspaces(ws_hash)
        );
        
        CREATE TABLE IF NOT EXISTS requests (
            request_id TEXT PRIMARY KEY,
            session_id TEXT,
            timestamp INTEGER,
            model_id TEXT,
            user_text TEXT,
            response_text TEXT,
            FOREIGN KEY (session_id) REFERENCES sessions(session_id)
        );
        
        CREATE VIRTUAL TABLE IF NOT EXISTS requests_fts USING fts5(
            user_text, response_text, content=requests, content_rowid=rowid
        );
        
        CREATE INDEX IF NOT EXISTS idx_sessions_last_msg ON sessions(last_msg_at DESC);
        CREATE INDEX IF NOT EXISTS idx_requests_model ON requests(model_id);
        CREATE INDEX IF NOT EXISTS idx_requests_session ON requests(session_id);
    """)
    conn.close()


def find_all_workspaces():
    """Find all workspace storage directories with chat sessions."""
    workspaces = []
    for ws in WORKSPACE_STORAGE.iterdir():
        if ws.is_dir():
            chat_dir = ws / "chatSessions"
            if chat_dir.exists() and list(chat_dir.glob("*.json")):
                workspaces.append((ws.name, ws, chat_dir))
    return workspaces


def extract_response_text(response: list) -> str:
    """Extract readable text from response parts.
    
    Response format (as of 2026):
    - thinking: AI reasoning/reflections (most valuable for search)
    - toolInvocationSerialized: tool calls with arguments
    - markdownContent/progressMessage: legacy formats
    """
    parts = []
    for item in response:
        if isinstance(item, dict):
            kind = item.get('kind', '')
            value = item.get('value', '')
            
            if kind in ('markdownContent', 'progressMessage') and isinstance(value, str):
                parts.append(value)
            elif kind == 'thinking' and isinstance(value, str) and len(value) > 10:
                parts.append(value)
            elif kind == 'toolInvocationSerialized':
                tool_data = item.get('toolSpecificData', {})
                if tool_data.get('kind') == 'terminal':
                    cmd = tool_data.get('commandLine', {})
                    if isinstance(cmd, dict):
                        cmd_text = cmd.get('original', '')
                        if cmd_text and ('journal' in cmd_text.lower() or 'remember' in cmd_text.lower() or len(cmd_text) > 200):
                            parts.append(f"[terminal] {cmd_text}")
    return '\n'.join(parts)


def index_session(conn: sqlite3.Connection, ws_hash: str, session_file: Path, force: bool = False) -> bool:
    """Index a single session file. Returns True if indexed."""
    mtime = session_file.stat().st_mtime
    existing = conn.execute(
        "SELECT file_mtime FROM sessions WHERE session_id = ?",
        (session_file.stem,)
    ).fetchone()
    
    if not force and existing and existing[0] == mtime:
        return False
    
    try:
        with open(session_file, encoding='utf-8') as f:
            data = json.load(f)
    except Exception:
        return False
    
    session_id = data.get('sessionId', session_file.stem)
    requests = data.get('requests', [])
    
    models = set()
    for req in requests:
        models.add(req.get('modelId', 'unknown'))
    
    conn.execute("""
        INSERT OR REPLACE INTO sessions 
        (session_id, ws_hash, title, created_at, last_msg_at, request_count, models, size_kb, file_mtime)
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
    """, (
        session_id, ws_hash, data.get('customTitle', 'Untitled'),
        data.get('creationDate'), data.get('lastMessageDate'),
        len(requests), json.dumps(list(models)),
        session_file.stat().st_size / 1024, mtime
    ))
    
    conn.execute("DELETE FROM requests WHERE session_id = ?", (session_id,))
    
    for req in requests:
        user_text = req.get('message', {}).get('text', '') if isinstance(req.get('message'), dict) else ''
        response_text = extract_response_text(req.get('response', []))
        
        conn.execute("""
            INSERT INTO requests (request_id, session_id, timestamp, model_id, user_text, response_text)
            VALUES (?, ?, ?, ?, ?, ?)
        """, (
            req.get('requestId'), session_id, req.get('timestamp'),
            req.get('modelId', 'unknown'), user_text, response_text
        ))
    
    return True


def update_index(force: bool = False, quiet: bool = True) -> int:
    """Update index with any new/changed sessions. Returns count indexed."""
    init_index_db()
    conn = sqlite3.connect(INDEX_DB)
    
    workspaces = find_all_workspaces()
    total_indexed = 0
    
    for ws_hash, ws_path, chat_dir in workspaces:
        conn.execute(
            "INSERT OR REPLACE INTO workspaces (ws_hash, path) VALUES (?, ?)",
            (ws_hash, str(ws_path))
        )
        
        for session_file in chat_dir.glob("*.json"):
            if index_session(conn, ws_hash, session_file, force=force):
                total_indexed += 1
    
    if total_indexed > 0:
        conn.execute("INSERT INTO requests_fts(requests_fts) VALUES('rebuild')")
    
    conn.commit()
    conn.close()
    
    if not quiet:
        print(f"Indexed {total_indexed} sessions across {len(workspaces)} workspaces")
    
    return total_indexed


# ═══════════════════════════════════════════════════════════════════════════════
# SEARCH
# ═══════════════════════════════════════════════════════════════════════════════

def search(query: str, limit: int = 3, context_chars: int = 300) -> list[dict]:
    """Search chat history, return most relevant recent matches."""
    update_index()  # Always update first (instant if no changes)
    
    if not INDEX_DB.exists():
        return []
    
    conn = sqlite3.connect(INDEX_DB)
    conn.row_factory = sqlite3.Row
    
    rows = conn.execute("""
        SELECT 
            r.session_id, r.timestamp, r.model_id,
            r.user_text, r.response_text, s.title
        FROM requests r
        JOIN sessions s ON r.session_id = s.session_id
        WHERE r.rowid IN (
            SELECT rowid FROM requests_fts WHERE requests_fts MATCH ?
        )
        ORDER BY r.timestamp DESC
        LIMIT ?
    """, (query, limit * 3)).fetchall()
    
    conn.close()
    
    results = []
    seen_content = set()
    
    for row in rows:
        user = row['user_text'] or ''
        response = row['response_text'] or ''
        query_lower = query.lower()
        
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
        })
        
        if len(results) >= limit:
            break
    
    return results


# ═══════════════════════════════════════════════════════════════════════════════
# UTILITIES
# ═══════════════════════════════════════════════════════════════════════════════

def stats():
    """Print statistics about indexed chats."""
    update_index()
    conn = sqlite3.connect(INDEX_DB)
    
    print("=== CHAT INDEX STATISTICS ===")
    
    total = conn.execute("SELECT COUNT(*) FROM sessions").fetchone()[0]
    print(f"Total sessions: {total}")
    
    print("\nRequests by model:")
    for row in conn.execute("""
        SELECT model_id, COUNT(*) as cnt 
        FROM requests GROUP BY model_id ORDER BY cnt DESC
    """):
        print(f"  {row[0]}: {row[1]}")
    
    size = conn.execute("SELECT SUM(size_kb) FROM sessions").fetchone()[0] or 0
    print(f"\nTotal chat data: {size/1024:.1f} MB")
    print(f"Index size: {INDEX_DB.stat().st_size/1024:.1f} KB")
    
    conn.close()


def export_model(model_filter: str, output_path: Path = None):
    """Export conversations for a specific model as JSONL."""
    update_index()
    
    if output_path is None:
        output_path = Path(f"{model_filter}_chats.jsonl")
    
    conn = sqlite3.connect(INDEX_DB)
    conn.row_factory = sqlite3.Row
    
    rows = conn.execute("""
        SELECT r.*, s.title
        FROM requests r
        JOIN sessions s ON r.session_id = s.session_id
        WHERE r.model_id LIKE ?
        ORDER BY r.timestamp
    """, (f'%{model_filter}%',)).fetchall()
    
    with open(output_path, 'w', encoding='utf-8') as f:
        for row in rows:
            entry = {
                'session': row['session_id'],
                'title': row['title'],
                'timestamp': row['timestamp'],
                'model': row['model_id'],
                'user': row['user_text'],
                'assistant': row['response_text'][:10000]
            }
            f.write(json.dumps(entry, ensure_ascii=False) + '\n')
    
    conn.close()
    print(f"Exported {len(rows)} requests to {output_path}")


def format_results(results: list[dict], query: str) -> str:
    """Format search results for display."""
    if not results:
        return f"No matches for '{query}'"
    
    lines = [f"=== Chat search: '{query}' ({len(results)} matches) ===\n"]
    
    for r in results:
        ts = r['timestamp'].strftime("%Y-%m-%d %H:%M") if r['timestamp'] else "unknown"
        lines.append(f"[{ts}] {r['model']} | {r['title'][:50]}")
        
        ctx = r['context'].replace('\n', ' ')
        if len(ctx) > 400:
            ctx = ctx[:400] + "..."
        
        lines.append(f"  {r['match_in'].upper()}: {ctx}")
        lines.append("")
    
    return '\n'.join(lines)


def main():
    import argparse
    parser = argparse.ArgumentParser(description="Search VS Code chat history")
    parser.add_argument('query', nargs='?', help='Search term')
    parser.add_argument('-n', '--limit', type=int, default=3, help='Max results')
    parser.add_argument('--json', action='store_true', help='Output as JSON')
    parser.add_argument('--stats', action='store_true', help='Show index statistics')
    parser.add_argument('--export', metavar='MODEL', help='Export model chats to JSONL')
    parser.add_argument('--reindex', action='store_true', help='Force full re-index')
    
    args = parser.parse_args()
    
    if args.reindex:
        update_index(force=True, quiet=False)
    elif args.stats:
        stats()
    elif args.export:
        export_model(args.export)
    elif args.query:
        results = search(args.query, limit=args.limit)
        if args.json:
            print(json.dumps(results, default=str, indent=2))
        else:
            print(format_results(results, args.query))
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
