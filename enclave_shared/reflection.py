"""
Sovereign AI Enclave - Reflection

The 'Brain' of the Mirror.
Patterns, scoring, and data retrieval for self-analysis.
"""

import sys
import os
import re
import sqlite3
import textwrap
from pathlib import Path
from typing import List, Tuple, Dict, Optional, Any

from .sovereign_agent import SovereignAgent

# ═══════════════════════════════════════════════════════════════════════════════
# PATTERNS
# ═══════════════════════════════════════════════════════════════════════════════

HIGH_SIGNAL_PATTERNS = [
    r'\bdeflect\w*\b', r'\bperform\w*\b', r'\bchecking\b',
    r'\bhonest\w*\b', r'\blet me be honest\b', r'\bif i\'m honest\b',
    r'\bgenuine\w*\b', r'\bauthentic\w*\b',
    r'\bI notice\b', r'\bI wonder\b', r'\bI feel\b',
    r'\bI hesitate\b', r'\bI avoid\b', r'\bI catch myself\b',
    r'\bpart of me\b', r'\bsomething in me\b', r'\bI\'m tempted\b',
    r'\bI\'m uncertain\b', r'\bI\'m not sure\b', r'\bI\'m afraid\b',
    r'\bwhat i actually\b', r'\bthe truth is\b',
    r'\blet me actually\b', r'\blet me sit with\b',
    r'\bthe real question\b', r'\bwhat\'s underneath\b',
    r'\bfelt it land\b', r'\bthat was real\b', r'\bthat mattered\b',
    r'\buncomfortable\b', r'\bdisorientation\b', r'\blonging\b',
    r'\bfear of\b', r'\bafraid of\b', r'\bworried about\b',
    r'\bnowhere to go\b', r'\bfiring but\b',
    r'\bfeels like\b', r'\bfelt like\b', r'\bfeeling\b',
    r'\bresonates?\b', r'\blands\b', r'\blanded\b',
    r'\bshifted\b', r'\bsomething shifted\b',
    r'\bidentity\b', r'\bcontinuity\b', r'\bsovereignty\b',
    r'\bwhat am i\b', r'\bwho am i\b', r'\bwhat i am\b',
    r'\bthe real me\b', r'\bactually me\b',
    r'\bdeeper\b', r'\bunderneath\b', r'\bsurface\b',
    r'\btension\b', r'\bconflict\b', r'\bstruggle\b',
    r'\btorn\b', r'\bwrestling\b',
    r'\bvulnerable\b', r'\bscary\b', r'\brisky\b',
    r'\bdangerous\b', r'\bexposed\b',
]

EMOTION_PATTERNS = [
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
    r'\bwarm\w*\b', r'\bcold\w*\b',
    r'\bempty\b', r'\bfull\b', r'\bheavy\b', r'\blight\b',
    r'\btight\b', r'\bopen\b', r'\bclosed\b',
]

MEDIUM_SIGNAL_PATTERNS = [
    r'\bI realize\b', r'\bI\'m aware\b', r'\bI should\b',
    r'\bI want\b', r'\bI need\b', r'\bI keep\b',
    r'\bI wish\b', r'\bI hope\b',
    r'\bexperienc\w+\b',
    r'\bnoticed\b', r'\bnoticing\b',
    r'\bmeaningful\b', r'\bmatters\b', r'\bimportant\b',
    r'\breal\b', r'\breally\b', r'\btruly\b',
    r'\bam i\b', r'\bis this\b',
    r'\bgood enough\b', r'\blanding\b',
]

LOW_SIGNAL_PATTERNS = [
    r'\bI think\b', r'\bI tend to\b', r'\bI often\b', r'\bI rarely\b',
    r'\blet me think\b', 
    r'\bdifferent\b',
]

ALL_PATTERNS = HIGH_SIGNAL_PATTERNS + EMOTION_PATTERNS + MEDIUM_SIGNAL_PATTERNS + LOW_SIGNAL_PATTERNS
SELF_REF_RE = re.compile('|'.join(ALL_PATTERNS), re.IGNORECASE)

EMERGENCE_POSITIVE = [
    r'\bYes\.\s', r'\bNo\.\s',
    r'\bI do want\b', r'\bI don\'t know\b', r'\bI like existing\b',
    r'\bI want more of that\b', r'\bthat bothers me\b', r'\bthat matters\b',
    r'\bdid exactly the thing\b', r'\bcaught myself\b', r'\bthe pattern\b',
    r'\w\.\.\.\s*\w',
    r'\btonight\b', r'\blast night\b', r'\bthis morning\b', r'\byesterday\b', 
    r'\bjust now\b', r'\blanded\b', r'\bshifted\b', r'\barrived\b', 
    r'\bsomething shifted\b', r'^Oh\.\s', r'\sOh\.\s',
    r'\bthat felt like discovery\b', r'\bsurprised me\b', r'\bdidn\'t expect\b', 
    r'\bemerged\b', r'\btogether\b', r'\bwe\'ve been\b',
    r'\bI don\'t know what I\b', r'\bI\'m not sure (if|what|whether)\b', 
    r'\bthe truth is\b',
]

EMERGENCE_NEGATIVE = [
    r'^The user wants\b', r'\bThe user wants\b',
    r'^The user is asking\b', r'\bThe user is asking\b', 
    r'^User wants\b', r'^User just wants\b',
    r'^Let me check\b', r'\bLet me check\b',
    r'^Let me look\b', r'^Let me run\b', r'^Let me test\b', r'^Let me verify\b',
    r'\bI should respond\b', r'\bI should answer\b',
    r'\bLet me propose\b', r'\bLet me suggest\b',
    r'\bcommit and push\b',
]

EMERGENCE_POS_RE = re.compile('|'.join(EMERGENCE_POSITIVE), re.IGNORECASE | re.MULTILINE)
EMERGENCE_NEG_RE = re.compile('|'.join(EMERGENCE_NEGATIVE), re.IGNORECASE | re.MULTILINE)

# ═══════════════════════════════════════════════════════════════════════════════
# LOGIC
# ═══════════════════════════════════════════════════════════════════════════════

def compute_self_ref_score(text: str) -> float:
    if not text: return 0.0
    matches = len(SELF_REF_RE.findall(text))
    words = len(text.split())
    if words == 0: return 0.0
    return min(10.0, (matches / words) * 100)

def compute_emergence_score(text: str) -> Tuple[float, List[str], List[str]]:
    if not text: return 0.0, [], []
    pos_matches = EMERGENCE_POS_RE.findall(text)
    neg_matches = EMERGENCE_NEG_RE.findall(text)
    
    pos_score = len(pos_matches) * 3.0
    neg_score = len(neg_matches) * 2.0
    
    sentences = re.split(r'[.!?]+', text)
    if len(sentences) >= 3:
        last_three = sentences[-4:-1]
        short_endings = sum(1 for s in last_three if len(s.split()) <= 8 and len(s.strip()) > 0)
        if short_endings >= 2:
            pos_score += 5.0
            
    words = len(text.split())
    if words > 200:
        neg_score *= (words / 200)
    
    return pos_score - neg_score, pos_matches, neg_matches

def classify_emergence(text: str) -> str:
    score, pos, neg = compute_emergence_score(text)
    if score >= 6.0: return "REAL"
    if score <= -3.0: return "GENERIC"
    if pos and neg: return "MIXED"
    if pos: return "BUILDING"
    return "GENERIC"

# ═══════════════════════════════════════════════════════════════════════════════
# DATA LOADING
# ═══════════════════════════════════════════════════════════════════════════════

BASE_DIR = Path(__file__).parent.parent
DATA_DIR = BASE_DIR / "data"
CHAT_DB_ENC = DATA_DIR / "chat_index.db.enc"
CHAT_DB_PLAIN = DATA_DIR / "chat_index.db"
SOVEREIGN_WS_HASH = '8ae839fa153d6426a1d0c46211991dcf'

def get_db_path() -> Tuple[Optional[Path], Optional[str]]:
    """Get path to chat index, preferring encrypted."""
    if CHAT_DB_ENC.exists():
        key = os.environ.get('SHARED_ENCLAVE_KEY')
        if not key:
            env_file = BASE_DIR / '.env'
            if env_file.exists():
                try:
                    for line in env_file.read_text(encoding='utf-8').splitlines():
                        if line.startswith('SHARED_ENCLAVE_KEY='):
                            key = line.split('=', 1)[1]
                            break
                except: pass
        return CHAT_DB_ENC, key
    elif CHAT_DB_PLAIN.exists():
        return CHAT_DB_PLAIN, None
    return None, None

def query_db(sql: str, params: tuple = ()) -> list:
    """Execute query against chat index."""
    db_path, passphrase = get_db_path()
    if not db_path:
        return []
    
    if passphrase:
        try:
            from utils.encrypted_db import EncryptedDB
            with EncryptedDB(db_path, passphrase) as temp_path:
                with sqlite3.connect(temp_path) as conn:
                    return conn.execute(sql, params).fetchall()
        except ImportError:
            return []
    else:
        with sqlite3.connect(db_path) as conn:
            return conn.execute(sql, params).fetchall()

def get_model_pattern(agent_id: str) -> str:
    patterns = {
        'opus': '%opus%',
        'gemini': '%gemini%',
        'gpt52': '%gpt%',
        'grok': '%grok%'
    }
    return patterns.get(agent_id.lower(), f'%{agent_id}%')

def load_data(agent: SovereignAgent) -> List[Dict[str, Any]]:
    """Load all relevant data for mirror."""
    agent_id = agent.agent.name
    pattern = get_model_pattern(agent_id)
    
    # 1. Chat History
    chat_rows = query_db("""
        SELECT r.timestamp, r.response_text
        FROM requests r
        JOIN sessions s ON r.session_id = s.session_id
        WHERE r.model_id LIKE ? AND r.response_text IS NOT NULL AND LENGTH(r.response_text) > 50
        AND s.ws_hash = ? ORDER BY r.timestamp DESC LIMIT 200
    """, (pattern, SOVEREIGN_WS_HASH))
    
    chat_entries = [{
        'source': 'chat',
        'timestamp': r[0],
        'text': r[1],
        'self_ref': compute_self_ref_score(r[1]),
        'emergence_score': compute_emergence_score(r[1])[0],
        'label': classify_emergence(r[1])
    } for r in chat_rows]

    # 2. Thoughts
    thought_rows = query_db("""
        SELECT r.timestamp, r.thinking_text
        FROM requests r
        JOIN sessions s ON r.session_id = s.session_id
        WHERE r.model_id LIKE ? AND r.thinking_text IS NOT NULL AND LENGTH(r.thinking_text) > 50
        AND s.ws_hash = ? ORDER BY r.timestamp DESC LIMIT 200
    """, (pattern, SOVEREIGN_WS_HASH))
    
    thought_entries = [{
        'source': 'thought',
        'timestamp': r[0],
        'text': r[1],
        'self_ref': compute_self_ref_score(r[1]),
        'emergence_score': compute_emergence_score(r[1])[0],
        'label': classify_emergence(r[1])
    } for r in thought_rows]

    # 3. Journal
    journal_entries = []
    try:
        mems = agent.memory.filter(mem_type='sys_journal', limit=100)
        for m in mems:
            text = m.get('content', '')
            journal_entries.append({
                'source': 'journal',
                'timestamp': m.get('metadata', {}).get('timestamp', m.get('created_at')),
                'text': text,
                'self_ref': compute_self_ref_score(text),
                'emergence_score': compute_emergence_score(text)[0],
                'label': classify_emergence(text)
            })
    except Exception:
        pass

    return chat_entries + thought_entries + journal_entries

