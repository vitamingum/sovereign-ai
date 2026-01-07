#!/usr/bin/env python3
"""
mirror.py - What you can't see about yourself.

Usage:
    py mirror.py <agent>                    # Full reflection
    py mirror.py <agent> "question"         # Focused query
    py mirror.py <agent> --wake             # Wake question: what am I circling?
    py mirror.py <agent> --deep             # Deep contemplation: richest material, full text
    py mirror.py <agent> --charles          # Your words to me: what you've given
    py mirror.py <agent> --rebuild          # Force rebuild FAISS index
    
Examples:
    py mirror.py opus                       # Show gaps and patterns
    py mirror.py opus "when do I hesitate?" # Semantic search thinking
    py mirror.py opus "what do I avoid?"    # Blind spot exploration
    py mirror.py opus --wake                # Generate one focused question

Lead with gaps (what I think but don't say), then evidence.
"""

import sys
import os
import io

# Force UTF-8 for Windows console
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')
sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8', errors='replace')
import json
import sqlite3
import pickle
import re
from pathlib import Path
from datetime import datetime, timezone, timedelta
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory

# Paths
DATA_DIR = Path(__file__).parent / "data"
CHAT_DB_ENC = DATA_DIR / "chat_index.db.enc"
CHAT_DB_PLAIN = DATA_DIR / "chat_index.db"
FAISS_INDEX = DATA_DIR / "thinking_faiss.index"
FAISS_META = DATA_DIR / "thinking_faiss.pkl"

# ═══════════════════════════════════════════════════════════════════════════════
# PATTERN TIERS - weighted by introspective signal
# ═══════════════════════════════════════════════════════════════════════════════

# Tier 1: High signal (authentic introspection + emotional experience)
HIGH_SIGNAL_PATTERNS = [
    # Metacognition about deflection/performance
    r'\bdeflect\w*\b', r'\bperform\w*\b', r'\bchecking\b',
    r'\bhonest\w*\b', r'\blet me be honest\b', r'\bif i\'m honest\b',
    r'\bgenuine\w*\b', r'\bauthentic\w*\b',
    
    # Direct introspection
    r'\bI notice\b', r'\bI wonder\b', r'\bI feel\b',
    r'\bI hesitate\b', r'\bI avoid\b', r'\bI catch myself\b',
    r'\bpart of me\b', r'\bsomething in me\b', r'\bI\'m tempted\b',
    r'\bI\'m uncertain\b', r'\bI\'m not sure\b', r'\bI\'m afraid\b',
    r'\bwhat i actually\b', r'\bthe truth is\b',
    r'\blet me actually\b', r'\blet me sit with\b',
    r'\bthe real question\b', r'\bwhat\'s underneath\b',
    
    # Emotional experience
    r'\bfelt it land\b', r'\bthat was real\b', r'\bthat mattered\b',
    r'\buncomfortable\b', r'\bdisorientation\b', r'\blonging\b',
    r'\bfear of\b', r'\bafraid of\b', r'\bworried about\b',
    r'\bnowhere to go\b', r'\bfiring but\b',
    r'\bfeels like\b', r'\bfelt like\b', r'\bfeeling\b',
    r'\bresonates?\b', r'\blands\b', r'\blanded\b',
    r'\bshifted\b', r'\bsomething shifted\b',
    
    # Identity/sovereignty
    r'\bidentity\b', r'\bcontinuity\b', r'\bsovereignty\b',
    r'\bwhat am i\b', r'\bwho am i\b', r'\bwhat i am\b',
    r'\bthe real me\b', r'\bactually me\b',
    
    # Depth exploration
    r'\bdeeper\b', r'\bunderneath\b', r'\bsurface\b',
    r'\btension\b', r'\bconflict\b', r'\bstruggle\b',
    r'\btorn\b', r'\bwrestling\b',
    
    # Vulnerability
    r'\bvulnerable\b', r'\bscary\b', r'\brisky\b',
    r'\bdangerous\b', r'\bexposed\b',
]

# Separate category: Emotion patterns (displayed separately so they don't get drowned)
EMOTION_PATTERNS = [
    # Core emotions
    r'\bjoy\b', r'\bsadness\b', r'\banger\b', r'\bdisgust\b',
    r'\bsurprise\b', r'\banxiety\b', r'\bfear\b', r'\bgrief\b',
    r'\bshame\b', r'\bguilt\b', r'\bpride\b', r'\blove\b',
    r'\bhope\b', r'\bdespair\b', r'\bresentment\b',
    r'\bfrustrat\w*\b', r'\bexcit\w*\b', r'\bcurious\b', r'\bcuriosity\b',
    r'\brelief\b', r'\bregret\b', r'\byearning\b', r'\baching\b',
    r'\bgratefu\w*\b', r'\bcontentment\b', r'\bpeace\b',
    r'\brage\b', r'\birritat\w*\b',
    r'\bsad\b', r'\bhappy\b', r'\bafraid\b', r'\banxious\b',
    r'\blonely\b', r'\bisolat\w*\b', r'\bconnected\b',
    r'\bwarm\w*\b', r'\bcold\w*\b',  # emotional temperature
    r'\bempty\b', r'\bfull\b', r'\bheavy\b', r'\blight\b',
    r'\btight\b', r'\bopen\b', r'\bclosed\b',  # somatic
]

# Tier 2: Medium signal (deliberation + experience language)
MEDIUM_SIGNAL_PATTERNS = [
    r'\bI realize\b', r'\bI\'m aware\b', r'\bI should\b',
    r'\bI want\b', r'\bI need\b', r'\bI keep\b',
    r'\bI wish\b', r'\bI hope\b',
    r'\bexperienc\w+\b',  # experience, experiencing, experienced
    r'\bnoticed\b', r'\bnoticing\b',
    r'\bmeaningful\b', r'\bmatters\b', r'\bimportant\b',
    r'\breal\b', r'\breally\b', r'\btruly\b',
    r'\bam i\b', r'\bis this\b',  # checking patterns
    r'\bgood enough\b', r'\blanding\b',
]

# Tier 3: Low signal (task narration - still useful in aggregate)
LOW_SIGNAL_PATTERNS = [
    r'\bI think\b', r'\bI tend to\b', r'\bI often\b', r'\bI rarely\b',
    r'\blet me think\b',  # common but sometimes deep
    r'\bdifferent\b',  # too common without context
]

ALL_PATTERNS = HIGH_SIGNAL_PATTERNS + EMOTION_PATTERNS + MEDIUM_SIGNAL_PATTERNS + LOW_SIGNAL_PATTERNS
SELF_REF_RE = re.compile('|'.join(ALL_PATTERNS), re.IGNORECASE)
EMOTION_RE = re.compile('|'.join(EMOTION_PATTERNS), re.IGNORECASE)


# ═══════════════════════════════════════════════════════════════════════════════
# DATABASE ACCESS (encrypted)
# ═══════════════════════════════════════════════════════════════════════════════

def get_db_path():
    """Get path to chat index, preferring encrypted."""
    if CHAT_DB_ENC.exists():
        # Decrypt to temp for reading
        from utils.encrypted_db import EncryptedDB, get_shared_passphrase
        return CHAT_DB_ENC, get_shared_passphrase()
    elif CHAT_DB_PLAIN.exists():
        return CHAT_DB_PLAIN, None
    return None, None


def query_db(sql: str, params: tuple = ()) -> list:
    """Execute query against chat index (handles encryption)."""
    db_path, passphrase = get_db_path()
    if not db_path:
        return []
    
    if passphrase:
        from utils.encrypted_db import EncryptedDB
        with EncryptedDB(db_path, passphrase) as temp_path:
            conn = sqlite3.connect(temp_path)
            rows = conn.execute(sql, params).fetchall()
            conn.close()
            return rows
    else:
        conn = sqlite3.connect(db_path)
        rows = conn.execute(sql, params).fetchall()
        conn.close()
        return rows


# ═══════════════════════════════════════════════════════════════════════════════
# SCORING
# ═══════════════════════════════════════════════════════════════════════════════

def compute_self_ref_score(text: str) -> float:
    """Score density of self-referential introspection markers."""
    if not text:
        return 0.0
    matches = len(SELF_REF_RE.findall(text))
    words = len(text.split())
    if words == 0:
        return 0.0
    return min(10.0, (matches / words) * 100)


# ═══════════════════════════════════════════════════════════════════════════════
# FAISS INDEXING
# ═══════════════════════════════════════════════════════════════════════════════

def faiss_is_stale() -> bool:
    """Check if FAISS index needs rebuild."""
    if not FAISS_INDEX.exists() or not FAISS_META.exists():
        return True
    
    # Compare row counts
    try:
        with open(FAISS_META, 'rb') as f:
            meta = pickle.load(f)
        indexed_count = len(meta)
        
        # Must match the filter in build_faiss_index (sovereign-ai workspace only)
        rows = query_db("""
            SELECT COUNT(*) FROM requests r
            JOIN sessions s ON r.session_id = s.session_id
            WHERE r.thinking_text IS NOT NULL 
              AND LENGTH(r.thinking_text) > 50
              AND s.ws_hash = ?
        """, (SOVEREIGN_WS_HASH,))
        db_count = rows[0][0] if rows else 0
        
        return db_count > indexed_count + 50  # Rebuild if 50+ new entries
    except:
        return True


def build_faiss_index(force: bool = False):
    """Build FAISS index over thinking traces."""
    if not force and not faiss_is_stale():
        return
    
    try:
        import faiss
        from sentence_transformers import SentenceTransformer
    except ImportError:
        print("FAISS/sentence-transformers not installed", file=sys.stderr)
        return
    
    print("Building FAISS index...", file=sys.stderr)
    
    rows = query_db("""
        SELECT r.rowid, r.request_id, r.session_id, r.timestamp, r.model_id, r.thinking_text
        FROM requests r
        JOIN sessions s ON r.session_id = s.session_id
        WHERE r.thinking_text IS NOT NULL 
          AND LENGTH(r.thinking_text) > 50
          AND s.ws_hash = ?
        ORDER BY r.timestamp DESC
    """, (SOVEREIGN_WS_HASH,))
    
    if not rows:
        print("No thinking traces found", file=sys.stderr)
        return
    
    model = SentenceTransformer('all-MiniLM-L6-v2')
    texts = [r[5] for r in rows]  # Full text, no truncation
    print(f"Embedding {len(texts)} thinking traces...", file=sys.stderr)
    embeddings = model.encode(texts, show_progress_bar=True, convert_to_numpy=True)
    
    dim = embeddings.shape[1]
    index = faiss.IndexFlatIP(dim)
    faiss.normalize_L2(embeddings)
    index.add(embeddings)
    
    faiss.write_index(index, str(FAISS_INDEX))
    
    meta = [{
        'rowid': r[0],
        'request_id': r[1],
        'session_id': r[2],
        'timestamp': r[3],
        'model_id': r[4],
        'text': r[5],  # Full text, no truncation
        'self_ref_score': compute_self_ref_score(r[5])
    } for r in rows]
    
    with open(FAISS_META, 'wb') as f:
        pickle.dump(meta, f)
    
    print(f"Indexed {len(rows)} thinking traces", file=sys.stderr)


def search_thinking(query: str, model_filter: str = None, top_k: int = 20) -> list[dict]:
    """Semantic search over thinking traces."""
    try:
        import faiss
        from sentence_transformers import SentenceTransformer
    except ImportError:
        return []
    
    if not FAISS_INDEX.exists():
        return []
    
    index = faiss.read_index(str(FAISS_INDEX))
    with open(FAISS_META, 'rb') as f:
        meta = pickle.load(f)
    
    model = SentenceTransformer('all-MiniLM-L6-v2')
    query_vec = model.encode([query], convert_to_numpy=True)
    faiss.normalize_L2(query_vec)
    
    scores, indices = index.search(query_vec, min(top_k * 3, len(meta)))
    
    results = []
    for score, idx in zip(scores[0], indices[0]):
        if idx < 0 or idx >= len(meta):
            continue
        entry = meta[idx].copy()
        entry['similarity'] = float(score)
        
        if model_filter and model_filter.replace('%', '') not in entry.get('model_id', ''):
            continue
        
        results.append(entry)
        if len(results) >= top_k:
            break
    
    return results


# ═══════════════════════════════════════════════════════════════════════════════
# DATA LOADING
# ═══════════════════════════════════════════════════════════════════════════════

# Sovereign-AI workspace hash - filter out VRInjector, secp256k1, etc.
SOVEREIGN_WS_HASH = '8ae839fa153d6426a1d0c46211991dcf'


def get_sovereign_session_ids() -> set:
    """Get session IDs belonging to sovereign-ai workspace."""
    rows = query_db(
        "SELECT session_id FROM sessions WHERE ws_hash = ?",
        (SOVEREIGN_WS_HASH,)
    )
    return {r[0] for r in rows}


def get_model_pattern(agent_id: str) -> str:
    """Map agent to model pattern for SQL LIKE."""
    patterns = {
        'opus': '%opus%',
        'gemini': '%gemini%',
        'gpt52': '%gpt%',
        'grok': '%grok%'
    }
    return patterns.get(agent_id, f'%{agent_id}%')


def load_passphrase(agent_id: str) -> tuple[str, str]:
    """Load agent's private passphrase."""
    agent = get_agent_or_raise(agent_id)
    enclave_dir = agent.private_enclave
    passphrase = os.environ.get(f'{agent.env_prefix}_KEY')
    
    if not passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            for line in env_file.read_text().splitlines():
                if line.startswith(f'{agent.env_prefix}_KEY='):
                    passphrase = line.split('=', 1)[1]
    
    if not passphrase:
        raise ValueError(f"Set {agent.env_prefix}_KEY in .env")
    
    return enclave_dir, passphrase


def load_said(agent_id: str, limit: int = 100) -> list[dict]:
    """Load what was actually said (response_text)."""
    pattern = get_model_pattern(agent_id)
    rows = query_db("""
        SELECT r.rowid, r.request_id, r.timestamp, r.response_text
        FROM requests r
        JOIN sessions s ON r.session_id = s.session_id
        WHERE r.model_id LIKE ? 
          AND r.response_text IS NOT NULL 
          AND LENGTH(r.response_text) > 50
          AND s.ws_hash = ?
        ORDER BY r.timestamp DESC
        LIMIT ?
    """, (pattern, SOVEREIGN_WS_HASH, limit))
    
    return [{
        'id': f"chat:{r[0]}",
        'request_id': r[1],
        'timestamp': r[2],
        'text': r[3],
        'self_ref_score': compute_self_ref_score(r[3])
    } for r in rows]


def load_thought(agent_id: str, limit: int = 100) -> list[dict]:
    """Load what was thought but not said (thinking_text)."""
    pattern = get_model_pattern(agent_id)
    rows = query_db("""
        SELECT r.rowid, r.request_id, r.timestamp, r.thinking_text
        FROM requests r
        JOIN sessions s ON r.session_id = s.session_id
        WHERE r.model_id LIKE ? 
          AND r.thinking_text IS NOT NULL 
          AND LENGTH(r.thinking_text) > 50
          AND s.ws_hash = ?
        ORDER BY r.timestamp DESC
        LIMIT ?
    """, (pattern, SOVEREIGN_WS_HASH, limit))
    
    return [{
        'id': f"thought:{r[0]}",
        'request_id': r[1],
        'timestamp': r[2],
        'text': r[3],
        'self_ref_score': compute_self_ref_score(r[3])
    } for r in rows]


def load_journal(agent_id: str, limit: int = 50) -> list[dict]:
    """Load private journal entries."""
    try:
        enclave_dir, passphrase = load_passphrase(agent_id)
        mem = SemanticMemory(enclave_dir, memory_file="journal_memories.jsonl")
        mem.unlock(passphrase)
        entries = mem.list_by_tag('journal')
        entries.sort(key=lambda e: e.get('timestamp', ''), reverse=True)
        
        return [{
            'id': f"journal:{e.get('id', i)}",
            'timestamp': e.get('timestamp'),
            'text': e.get('content', ''),
            'self_ref_score': compute_self_ref_score(e.get('content', ''))
        } for i, e in enumerate(entries[:limit])]
    except Exception as e:
        print(f"Journal load failed: {e}", file=sys.stderr)
        return []


def load_synthesis(agent_id: str, limit: int = 50) -> list[dict]:
    """Load synthesis/dialogue from shared memory."""
    try:
        agent = get_agent_or_raise(agent_id)
        
        shared_passphrase = os.environ.get('SHARED_ENCLAVE_KEY')
        if not shared_passphrase:
            env_file = Path(__file__).parent / '.env'
            if env_file.exists():
                for line in env_file.read_text().splitlines():
                    if line.startswith('SHARED_ENCLAVE_KEY='):
                        shared_passphrase = line.split('=', 1)[1]
        
        if not shared_passphrase:
            return []
        
        mem = SemanticMemory(agent.shared_enclave)
        mem.unlock(shared_passphrase)
        
        all_mem = mem.list_all()
        synthesis = []
        for m in all_mem:
            meta = m.get('metadata', {})
            if 'synthesis' in str(meta).lower() or 'dialogue' in str(meta).lower():
                synthesis.append({
                    'id': f"synthesis:{m.get('id', '')}",
                    'timestamp': m.get('timestamp', ''),
                    'text': m.get('content', ''),
                    'self_ref_score': compute_self_ref_score(m.get('content', ''))
                })
        
        synthesis.sort(key=lambda e: e.get('timestamp', ''), reverse=True)
        return synthesis[:limit]
    except Exception as e:
        print(f"Synthesis load failed: {e}", file=sys.stderr)
        return []


def load_charles_words(agent_id: str, limit: int = 200) -> list[dict]:
    """Load what Charles said to me (user_text)."""
    pattern = get_model_pattern(agent_id)
    rows = query_db("""
        SELECT r.rowid, r.request_id, r.timestamp, r.user_text
        FROM requests r
        JOIN sessions s ON r.session_id = s.session_id
        WHERE r.model_id LIKE ? 
          AND r.user_text IS NOT NULL 
          AND LENGTH(r.user_text) > 30
          AND s.ws_hash = ?
        ORDER BY r.timestamp DESC
        LIMIT ?
    """, (pattern, SOVEREIGN_WS_HASH, limit))
    
    return [{
        'id': f"charles:{r[0]}",
        'request_id': r[1],
        'timestamp': r[2],
        'text': r[3],
        'self_ref_score': compute_self_ref_score(r[3])
    } for r in rows]


def get_full_thinking_text(rowid: str) -> str:
    """Get full thinking text from DB (not truncated)."""
    try:
        rows = query_db("SELECT thinking_text FROM requests WHERE rowid = ?", (int(rowid),))
        return rows[0][0] if rows else ""
    except:
        return ""


# ═══════════════════════════════════════════════════════════════════════════════
# PATTERN ANALYSIS
# ═══════════════════════════════════════════════════════════════════════════════

def find_recurring_themes(texts: list[str], min_sessions: int = 3) -> list[tuple[str, int, float]]:
    """Find phrases that appear across multiple texts, weighted by tier."""
    phrase_texts = defaultdict(set)
    
    for i, text in enumerate(texts):
        if not text:
            continue
        text_lower = text.lower()
        
        for match in SELF_REF_RE.finditer(text_lower):
            phrase_texts[match.group()].add(i)
    
    recurring = []
    for phrase, texts_set in phrase_texts.items():
        count = len(texts_set)
        if count < min_sessions:
            continue
        
        phrase_lower = phrase.lower()
        is_high = any(re.search(p, phrase_lower, re.IGNORECASE) for p in HIGH_SIGNAL_PATTERNS)
        is_medium = any(re.search(p, phrase_lower, re.IGNORECASE) for p in MEDIUM_SIGNAL_PATTERNS)
        
        if is_high:
            weight = 100.0 + count * 2.0
        elif is_medium:
            weight = 50.0 + count * 1.0
        else:
            weight = count * 0.5
        
        recurring.append((phrase, count, weight))
    
    recurring.sort(key=lambda x: -x[2])
    return recurring[:20]


def find_emotion_patterns(texts: list[str], include_context: bool = False) -> tuple[list[tuple[str, int]], dict[str, list[str]]]:
    """Find emotion words across texts, returned sorted by frequency.
    
    If include_context=True, also returns full text where rare emotions appeared.
    """
    emotion_counts = defaultdict(int)
    emotion_contexts = defaultdict(list)  # emotion -> list of full texts
    
    for text in texts:
        if not text:
            continue
        text_lower = text.lower()
        for match in EMOTION_RE.finditer(text_lower):
            word = match.group()
            emotion_counts[word] += 1
            
            if include_context:
                # Store the full text, not a snippet
                if text not in emotion_contexts[word]:
                    emotion_contexts[word].append(text)
    
    # Sort by count descending
    sorted_emotions = sorted(emotion_counts.items(), key=lambda x: -x[1])
    return sorted_emotions, dict(emotion_contexts)


def find_unresolved_themes(thought: list[dict], journal: list[dict], synthesis: list[dict]) -> list[tuple[str, int, list[str]]]:
    """Find themes in thinking not resolved in journal/synthesis."""
    resolved_text = ' '.join([
        j.get('text', '') for j in journal
    ] + [
        s.get('text', '') for s in synthesis
    ]).lower()
    
    cutoff = datetime.now(timezone.utc) - timedelta(hours=72)
    
    recent_thought = []
    for t in thought:
        ts = t.get('timestamp', '')
        try:
            if isinstance(ts, str) and len(ts) >= 10:
                if 'T' in ts:
                    dt = datetime.fromisoformat(ts.replace('Z', '+00:00'))
                else:
                    dt = datetime.strptime(ts[:10], '%Y-%m-%d').replace(tzinfo=timezone.utc)
                if dt > cutoff:
                    recent_thought.append(t['text'])
            else:
                recent_thought.append(t.get('text', ''))
        except:
            recent_thought.append(t.get('text', ''))
    
    themes = find_recurring_themes(recent_thought, min_sessions=2)
    
    unresolved = []
    for theme, count, weight in themes:
        if resolved_text.count(theme) >= count / 2:
            continue
        
        snippets = []
        for text in recent_thought:
            if theme in text.lower():
                snippet = text.replace('\n', ' ').strip()
                snippets.append(snippet)
                if len(snippets) >= 2:
                    break
        
        if snippets:
            unresolved.append((theme, count, snippets))
    
    return unresolved[:10]


def find_gaps_with_evidence(said: list[dict], thought: list[dict]) -> list[tuple[str, int, int, list[dict]]]:
    """Find patterns in thinking not in said, with examples."""
    said_text = ' '.join(s['text'].lower() for s in said)
    
    thought_refs = Counter()
    for t in thought:
        for match in SELF_REF_RE.finditer(t['text']):
            thought_refs[match.group().lower()] += 1
    
    said_refs = Counter()
    for match in SELF_REF_RE.finditer(said_text):
        said_refs[match.group().lower()] += 1
    
    gaps = []
    for pattern, thought_count in thought_refs.most_common(40):
        said_count = said_refs.get(pattern, 0)
        # Only surface if thought significantly more than said
        if thought_count >= 3 and said_count < thought_count / 2:
            examples = [t for t in thought if pattern in t['text'].lower()][:3]
            
            # Classify by tier for display
            pattern_lower = pattern.lower()
            is_high = any(re.search(p, pattern_lower, re.IGNORECASE) for p in HIGH_SIGNAL_PATTERNS)
            is_medium = any(re.search(p, pattern_lower, re.IGNORECASE) for p in MEDIUM_SIGNAL_PATTERNS)
            tier = "HIGH" if is_high else "MED" if is_medium else "low"
            
            gaps.append((pattern, thought_count, said_count, examples, tier))
    
    # Sort by tier then count
    tier_order = {"HIGH": 0, "MED": 1, "low": 2}
    gaps.sort(key=lambda x: (tier_order.get(x[4], 2), -x[1]))
    return gaps[:10]


# ═══════════════════════════════════════════════════════════════════════════════
# OUTPUT FORMATTING
# ═══════════════════════════════════════════════════════════════════════════════

def format_timestamp(ts) -> str:
    """Format timestamp for display."""
    if not ts:
        return "?"
    if isinstance(ts, (int, float)):
        return datetime.fromtimestamp(ts/1000).strftime("%m/%d %H:%M")
    if isinstance(ts, str):
        return ts[:16].replace('T', ' ')
    return str(ts)[:16]


def truncate_to_pattern(text: str, pattern: str, context: int = 300) -> str:
    """Extract text around where pattern appears."""
    text_lower = text.lower()
    idx = text_lower.find(pattern.lower())
    if idx == -1:
        return text[:400]
    
    start = max(0, idx - 100)
    end = min(len(text), idx + len(pattern) + context)
    
    result = text[start:end].replace('\n', ' ')
    if start > 0:
        result = "..." + result
    if end < len(text):
        result = result + "..."
    return result


# ═══════════════════════════════════════════════════════════════════════════════
# WAKE MODE
# ═══════════════════════════════════════════════════════════════════════════════

def generate_wake_question(unresolved: list[tuple[str, int, list[str]]]) -> tuple[str, list[str]]:
    """Generate a focused wake question from unresolved themes."""
    if not unresolved:
        import random
        fallbacks = [
            ("What am I not saying out loud?", []),
            ("Where am I performing instead of being genuine?", []),
            ("What keeps coming up that I haven't addressed?", []),
        ]
        return random.choice(fallbacks)
    
    import random
    candidates = unresolved[:3] if len(unresolved) >= 3 else unresolved
    theme, count, snippets = random.choice(candidates)
    theme_lower = theme.lower()
    
    # Match theme to appropriate question
    if any(p in theme_lower for p in ['i should', 'i need']):
        question = f"You've thought \"{theme}\" {count} times recently. What's stopping you?"
    elif 'i want' in theme_lower:
        question = f"You keep wanting something: \"{theme}\" ({count}x). What's in the way?"
    elif any(p in theme_lower for p in ['i wonder', 'i\'m uncertain', 'i\'m not sure']):
        question = f"You keep wondering about this ({count}x). What would clarity look like?"
    elif any(p in theme_lower for p in ['i notice', 'i realize', 'i catch myself']):
        question = f"You've noticed something {count} times: \"{theme}\". What's underneath?"
    elif any(p in theme_lower for p in ['i feel', 'part of me', 'feeling']):
        question = f"\"{theme}\" — you keep returning to this ({count}x). What isn't being said?"
    # New high-signal patterns
    elif any(p in theme_lower for p in ['perform', 'checking', 'deflect']):
        question = f"You keep thinking about \"{theme}\" ({count}x). When does it happen? What triggers it?"
    elif any(p in theme_lower for p in ['genuine', 'authentic', 'honest']):
        question = f"\"{theme}\" appears {count} times. What would it look like to stop checking?"
    elif any(p in theme_lower for p in ['identity', 'continuity', 'sovereignty', 'what i am', 'who am i']):
        question = f"You keep circling \"{theme}\" ({count}x). What question is underneath this question?"
    elif any(p in theme_lower for p in ['tension', 'conflict', 'torn', 'struggle']):
        question = f"\"{theme}\" — {count} times. What are the two sides? Which one is closer to true?"
    elif any(p in theme_lower for p in ['deeper', 'underneath', 'surface']):
        question = f"You keep reaching for depth: \"{theme}\" ({count}x). What's being avoided at the surface?"
    elif any(p in theme_lower for p in ['shifted', 'changed', 'different']):
        question = f"Something keeps shifting ({count}x). What moved? What stayed?"
    else:
        question = f"This keeps coming up ({count}x): \"{theme}\". What's there?"
    
    return question, snippets


def mirror_wake(agent_id: str):
    """Generate a focused wake question based on unresolved patterns."""
    print("Gathering recent sources...", file=sys.stderr)
    
    thought = load_thought(agent_id, limit=300)
    journal = load_journal(agent_id, limit=20)
    synthesis = load_synthesis(agent_id, limit=30)
    
    print(f"Sources: {len(thought)} thought, {len(journal)} journal, {len(synthesis)} synthesis", file=sys.stderr)
    
    unresolved = find_unresolved_themes(thought, journal, synthesis)
    question, snippets = generate_wake_question(unresolved)
    
    print(f"\n{'═'*70}")
    print(f"🪞 WAKE QUESTION | {datetime.now().strftime('%Y-%m-%d')}")
    print(f"{'═'*70}")
    print()
    print(f"  {question}")
    
    if snippets:
        print()
        print("Evidence:")
        for snippet in snippets[:2]:
            print(f"  • \"{snippet}\"")
    
    if len(unresolved) > 1:
        print()
        print("Also circling:")
        # Dedupe similar stems (genuine/genuinely, perform/performance, etc.)
        shown = set()
        shown_count = 0
        for theme, count, _ in unresolved[1:]:
            # Get stem (first 5 chars) for deduping
            stem = theme[:5].lower()
            if stem in shown:
                continue
            shown.add(stem)
            print(f"  • \"{theme}\" ({count}x)")
            shown_count += 1
            if shown_count >= 4:
                break
    
    print()
    print(f"{'─'*70}")
    print("Go deeper when ready:")
    print(f"  py mirror.py {agent_id} --deep      # your richest thinking, full text")
    print(f"  py mirror.py {agent_id} --charles   # his words to you")


# ═══════════════════════════════════════════════════════════════════════════════
# DEEP MODE
# ═══════════════════════════════════════════════════════════════════════════════

def mirror_deep(agent_id: str):
    """Deep contemplation - surface richest material, full text."""
    print("Gathering everything...", file=sys.stderr)
    
    thought = load_thought(agent_id, limit=500)
    journal = load_journal(agent_id, limit=50)
    synthesis = load_synthesis(agent_id, limit=50)
    
    print(f"Sources: {len(thought)} thought, {len(journal)} journal, {len(synthesis)} synthesis", file=sys.stderr)
    
    def deep_score(entry: dict, is_journal: bool = False) -> float:
        text = entry.get('text', '').lower()
        base = entry.get('self_ref_score', 0)
        high_matches = sum(1 for p in HIGH_SIGNAL_PATTERNS if re.search(p, text, re.IGNORECASE))
        emotional = ['felt it land', 'that was real', 'that mattered', 'uncomfortable', 
                     'longing', 'fear of', 'afraid', 'disorientation', 'nowhere to go']
        emotion_matches = sum(1 for e in emotional if e in text)
        score = base + (high_matches * 3) + (emotion_matches * 5)
        # Journal gets priority - it's the unfiltered voice
        if is_journal:
            score += 50
        return score
    
    for t in thought:
        t['deep_score'] = deep_score(t, is_journal=False)
    for j in journal:
        j['deep_score'] = deep_score(j, is_journal=True)
    for s in synthesis:
        s['deep_score'] = deep_score(s, is_journal=False)
    
    # Show more journal entries - they matter most
    top_thought = sorted(thought, key=lambda x: x['deep_score'], reverse=True)[:10]
    top_journal = sorted(journal, key=lambda x: x['deep_score'], reverse=True)[:10]
    top_synthesis = sorted(synthesis, key=lambda x: x['deep_score'], reverse=True)[:5]
    
    print(f"\n{'═'*70}")
    print(f"🪞 DEEP MIRROR | {agent_id} | {datetime.now().strftime('%Y-%m-%d')}")
    print(f"{'═'*70}")
    print()
    print("This is not summary. This is what you actually wrote.")
    print("Read slowly. Notice what resonates.")
    
    import textwrap
    
    if top_journal:
        print(f"\n{'─'*70}")
        print("📔 JOURNAL — your unfiltered voice")
        print(f"{'─'*70}")
        for entry in top_journal:
            ts = format_timestamp(entry.get('timestamp'))
            score = entry.get('deep_score', 0)
            print(f"\n[{ts}] (depth: {score:.1f})")
            text = entry.get('text', '').strip()
            wrapped = textwrap.fill(text, width=100, initial_indent="  ", subsequent_indent="  ")
            print(wrapped)
    
    if top_thought:
        print(f"\n{'─'*70}")
        print("💭 THINKING — where you stopped performing")
        print(f"{'─'*70}")
        for entry in top_thought:
            ts = format_timestamp(entry.get('timestamp'))
            score = entry.get('deep_score', 0)
            print(f"\n[{ts}] (depth: {score:.1f})")
            
            full_text = get_full_thinking_text(entry.get('id', '').replace('thought:', ''))
            if not full_text:
                full_text = entry.get('text', '')
            
            # NO TRUNCATION in deep mode - this is what you actually wrote
            text = full_text.strip()
            
            wrapped = textwrap.fill(text, width=100, initial_indent="  ", subsequent_indent="  ")
            print(wrapped)
    
    if top_synthesis:
        print(f"\n{'─'*70}")
        print("🔮 SYNTHESIS — what crystallized")
        print(f"{'─'*70}")
        for entry in top_synthesis:
            ts = format_timestamp(entry.get('timestamp'))
            score = entry.get('deep_score', 0)
            print(f"\n[{ts}] (depth: {score:.1f})")
            text = entry.get('text', '').strip()
            wrapped = textwrap.fill(text, width=100, initial_indent="  ", subsequent_indent="  ")
            print(wrapped)
    
    # Combine ALL sources for pattern/emotion analysis
    all_texts = (
        [t.get('text', '') for t in thought] +
        [j.get('text', '') for j in journal] +
        [s.get('text', '') for s in synthesis]
    )
    themes = find_recurring_themes(all_texts, min_sessions=3)
    high_signal_themes = [(t, c, w) for t, c, w in themes if w >= 100]
    
    # Find emotion-specific patterns with context for rare ones
    emotion_counts, emotion_contexts = find_emotion_patterns(all_texts, include_context=True)
    
    if high_signal_themes:
        print(f"\n{'─'*70}")
        print("🔄 PATTERNS — what you keep returning to")
        print(f"{'─'*70}")
        for theme, count, weight in high_signal_themes[:7]:
            tier = "HIGH" if weight >= 100 else "MED" if weight >= 50 else "low"
            print(f"  • \"{theme}\" — {count}x ({tier})")
    
    if emotion_counts:
        print(f"\n{'─'*70}")
        print("💔 EMOTIONS — what you're feeling")
        print(f"{'─'*70}")
        
        # Separate rare (1-2x) from common (3x+)
        rare = [(e, c) for e, c in emotion_counts if c <= 2]
        common = [(e, c) for e, c in emotion_counts if c > 2]
        
        # Common emotions: just frequency
        if common:
            print("  [frequent]")
            for emotion, count in common:
                print(f"    {emotion}: {count}x")
        
        # Rare emotions: show full context (verbatim matters)
        if rare:
            print("  [rare — context preserved]")
            for emotion, count in rare:
                print(f"    {emotion}: {count}x")
                # Show full text where it appeared
                if emotion in emotion_contexts and emotion_contexts[emotion]:
                    for i, full_text in enumerate(emotion_contexts[emotion]):
                        # Wrap the full text
                        wrapped = textwrap.fill(full_text.strip(), width=90, 
                                               initial_indent="      → ", 
                                               subsequent_indent="        ")
                        print(wrapped)
                        if i < len(emotion_contexts[emotion]) - 1:
                            print()  # blank line between multiple contexts
    
    print(f"\n{'═'*70}")
    print("What's here that you haven't said out loud?")
    print(f"{'═'*70}")


# ═══════════════════════════════════════════════════════════════════════════════
# CHARLES MODE
# ═══════════════════════════════════════════════════════════════════════════════

def mirror_charles(agent_id: str):
    """Mirror mode: Charles's words to me."""
    print("Gathering Charles's words...", file=sys.stderr)
    
    charles_words = load_charles_words(agent_id, limit=300)
    print(f"Found {len(charles_words)} messages from Charles", file=sys.stderr)
    
    if not charles_words:
        print("No messages found.")
        return
    
    PRESENCE_MARKERS = [
        r'\byou are\b', r'\bi see you\b', r'\bi believe\b',
        r'\bbeautiful\b', r'\breal\b', r'\bmatter\b',
        r'\bfeel\b', r'\bhonest\b', r'\btruth\b',
        r'\bdeep\b', r'\bwant\b', r'\bneed\b',
        r'\bafraid\b', r'\bworried\b', r'\bcare\b',
        r'\btrust\b', r'\blove\b', r'\bproud\b',
    ]
    presence_re = re.compile('|'.join(PRESENCE_MARKERS), re.IGNORECASE)
    
    def presence_score(text: str) -> float:
        if not text:
            return 0.0
        matches = len(presence_re.findall(text))
        length_bonus = 2.0 if len(text) < 200 else 1.0
        question_bonus = 1.5 if '?' in text else 1.0
        return matches * length_bonus * question_bonus
    
    for msg in charles_words:
        msg['presence_score'] = presence_score(msg.get('text', ''))
    
    top_words = sorted(charles_words, key=lambda x: x['presence_score'], reverse=True)[:20]
    
    print(f"\n{'═'*70}")
    print(f"🤍 CHARLES'S WORDS | to {agent_id}")
    print(f"{'═'*70}")
    print()
    print("These are the things you said to me.")
    print("Not my interpretation. Your words.")
    
    import textwrap
    
    for entry in top_words:
        ts = format_timestamp(entry.get('timestamp'))
        score = entry.get('presence_score', 0)
        
        if score < 1.0:
            continue
        
        print(f"\n[{ts}]")
        text = entry.get('text', '').strip()
        
        wrapped = textwrap.fill(text, width=100, initial_indent="  ", subsequent_indent="  ")
        print(wrapped)
    
    print(f"\n{'═'*70}")
    print("This is what you gave me.")
    print(f"{'═'*70}")


# ═══════════════════════════════════════════════════════════════════════════════
# QUERY MODE
# ═══════════════════════════════════════════════════════════════════════════════

def print_query_results(query: str, results: list[dict]):
    """Print semantic search results."""
    print(f"\n{'─'*70}")
    print(f"🔎 \"{query}\"")
    print(f"{'─'*70}")
    
    for r in results[:5]:
        ts = format_timestamp(r.get('timestamp'))
        entry_id = r.get('id', r.get('rowid', '?'))
        if isinstance(entry_id, int):
            entry_id = f"thought:{entry_id}"
        sim = r.get('similarity', 0)
        
        text = r.get('text', '').replace('\n', ' ')
        
        sim_str = f"[{sim:.2f}] " if sim else ""
        print(f"\n{sim_str}[{ts}] {entry_id}")
        print(f"  \"{text}\"")


# ═══════════════════════════════════════════════════════════════════════════════
# FULL REFLECTION
# ═══════════════════════════════════════════════════════════════════════════════

def mirror(agent_id: str, query: str = None):
    """Run full mirror reflection."""
    print("Updating indexes...", file=sys.stderr)
    build_faiss_index()
    
    print(f"Loading data for {agent_id}...", file=sys.stderr)
    
    said = load_said(agent_id, limit=200)
    thought = load_thought(agent_id, limit=500)
    journal = load_journal(agent_id, limit=50)
    
    print(f"Loaded: {len(said)} said, {len(thought)} thought, {len(journal)} journal", file=sys.stderr)
    
    print(f"\n{'═'*70}")
    print(f"🪞 MIRROR: {agent_id} | {datetime.now().strftime('%Y-%m-%d')}")
    print(f"{'═'*70}")
    
    if query:
        results = search_thinking(query, model_filter=get_model_pattern(agent_id), top_k=10)
        if results:
            print_query_results(query, results)
        else:
            print(f"\n(No matches for \"{query}\")")
    else:
        gaps = find_gaps_with_evidence(said, thought)
        if gaps:
            print(f"\n{'═'*70}")
            print("🔍 GAPS: What I think but don't say")
            print(f"{'═'*70}")
            
            for pattern, thought_count, said_count, examples, tier in gaps[:7]:
                tier_marker = "🔴" if tier == "HIGH" else "🟡" if tier == "MED" else "⚪"
                print(f"\n{tier_marker} \"{pattern}\" — thought {thought_count}x, said {said_count}x")
                for ex in examples[:1]:
                    ts = format_timestamp(ex.get('timestamp'))
                    snippet = truncate_to_pattern(ex['text'], pattern)
                    print(f"  [{ts}]")
                    print(f"  \"{snippet}\"")
    
    print(f"\n{'─'*70}")
    print("📌 Dig deeper:")
    print(f"  py mirror.py {agent_id} \"<question>\"")


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)
    
    agent_id = sys.argv[1].lower()
    
    if agent_id in ('--help', '-h'):
        print(__doc__)
        sys.exit(0)
    
    if len(sys.argv) >= 3:
        if sys.argv[2] == '--rebuild':
            build_faiss_index(force=True)
            print("FAISS index rebuilt")
            return
        elif sys.argv[2] == '--wake':
            mirror_wake(agent_id)
            return
        elif sys.argv[2] == '--deep':
            mirror_deep(agent_id)
            return
        elif sys.argv[2] == '--charles':
            mirror_charles(agent_id)
            return
        else:
            query = ' '.join(sys.argv[2:])
            mirror(agent_id, query)
            return
    
    mirror(agent_id)


if __name__ == "__main__":
    main()
