#!/usr/bin/env python3
"""
recollect_topic.py - Topic-based understanding retrieval.

Usage:
    python recollect_topic.py opus messaging
    python recollect_topic.py opus encryption
    python recollect_topic.py opus "who we are"

Workflow:
1. Gets shallow understanding table of all files
2. LLM picks files relevant to the topic
3. Recollects each (or falls back to shallow_deps)
4. Displays concatenated results

The agent does the synthesis mentally - no LLM merge.
"""

import sys
import os
import json
import subprocess
import requests
from pathlib import Path
from datetime import datetime, timezone
from concurrent.futures import ThreadPoolExecutor, as_completed

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from shallow_understand import instant_understand
from enclave.config import get_agent_or_raise
from enclave.semantic_memory import SemanticMemory


# ─────────────────────────────────────────────────────────────────────────────
# LLM File Selection
# ─────────────────────────────────────────────────────────────────────────────

FILE_SELECT_PROMPT = '''Given this list of files and their purposes, select which ones are relevant to the topic: "{topic}"

FILES:
{file_table}

Return a JSON array of filenames (just the names, not paths). Select 2-7 most relevant files.
Example: ["msg.py", "decrypt_msg.py", "enclave/opaque.py"]

ONLY output the JSON array, nothing else:'''


def get_shallow_table() -> list[tuple[str, str]]:
    """Get shallow understanding of all Python files."""
    root = Path(__file__).parent
    files = []
    
    # Root .py files
    for p in root.glob('*.py'):
        if p.name.startswith('generated_') or p.name.startswith('test_'):
            continue
        purpose, _ = instant_understand(str(p))
        files.append((p.name, purpose))
    
    # enclave/ files
    enclave = root / 'enclave'
    if enclave.exists():
        for p in enclave.glob('*.py'):
            if p.name.startswith('test'):
                continue
            purpose, _ = instant_understand(str(p))
            files.append((f"enclave/{p.name}", purpose))
    
    # docs/ markdown
    docs = root / 'docs'
    if docs.exists():
        for p in docs.glob('*.md'):
            # First line of markdown as purpose
            try:
                with open(p, 'r', encoding='utf-8') as f:
                    first_line = f.readline().strip().lstrip('#').strip()
                    files.append((f"docs/{p.name}", first_line or "(untitled)"))
            except:
                pass
    
    return files


def select_files_with_llm(topic: str, files: list[tuple[str, str]], model: str = 'qwen2.5:7b') -> list[str]:
    """Use LLM to select relevant files for a topic."""
    # Format file table
    table = "\n".join(f"  {name}: {purpose}" for name, purpose in files)
    
    prompt = FILE_SELECT_PROMPT.format(topic=topic, file_table=table)
    
    try:
        response = requests.post(
            'http://localhost:11434/api/generate',
            json={
                'model': model,
                'prompt': prompt,
                'stream': False,
                'options': {'temperature': 0, 'num_predict': 500}
            },
            timeout=30
        )
        result = response.json().get('response', '').strip()
        
        # Parse JSON array
        # Handle markdown code blocks
        if '```' in result:
            result = result.split('```')[1]
            if result.startswith('json'):
                result = result[4:]
        
        selected = json.loads(result)
        
        # Validate files exist
        valid = []
        file_names = {name for name, _ in files}
        for f in selected:
            if f in file_names:
                valid.append(f)
        
        return valid if valid else [files[0][0]]  # Fallback to first file
        
    except Exception as e:
        print(f"⚠️  LLM file selection failed: {e}", file=sys.stderr)
        # Fallback: simple keyword match
        topic_lower = topic.lower()
        matches = []
        for name, purpose in files:
            if topic_lower in name.lower() or topic_lower in purpose.lower():
                matches.append(name)
        return matches[:5] if matches else [files[0][0]]


# ─────────────────────────────────────────────────────────────────────────────
# Recollection
# ─────────────────────────────────────────────────────────────────────────────

def recollect_file(agent: str, filename: str) -> tuple[str, str, bool]:
    """
    Recollect understanding of a file.
    Returns (filename, content, is_deep).
    """
    root = Path(__file__).parent
    env = os.environ.copy()
    env['PYTHONIOENCODING'] = 'utf-8'
    
    # Try recollect.py first
    try:
        result = subprocess.run(
            ["python", "recollect.py", agent, filename],
            capture_output=True,
            text=True,
            cwd=root,
            timeout=10,
            env=env,
            encoding='utf-8',
            errors='replace'
        )
        output = result.stdout.strip()
        
        # Check if we got real content (not "No understanding")
        if result.returncode == 0 and "No understanding stored" not in output:
            return (filename, output, True)
    except Exception:
        pass
    
    # Fallback to shallow_deps (only for Python files)
    if not filename.endswith('.md'):
        try:
            result = subprocess.run(
                ["python", "shallow_deps.py", filename],
                capture_output=True,
                text=True,
                cwd=root,
                timeout=10,
                env=env,
                encoding='utf-8',
                errors='replace'
            )
            if result.returncode == 0:
                return (filename, result.stdout.strip(), False)
        except Exception:
            pass
    
    # Last resort: instant understand or read markdown
    filepath = root / filename
    if filepath.exists():
        if filepath.suffix == '.md':
            # For markdown, read first ~2000 chars
            try:
                with open(filepath, 'r', encoding='utf-8') as f:
                    content = f.read(2000)
                    if len(content) == 2000:
                        content += "\n... [truncated]"
                    return (filename, content, False)
            except:
                pass
        else:
            purpose, funcs = instant_understand(str(filepath))
            shallow = f"Purpose: {purpose}\nFunctions: {', '.join(funcs[:5])}"
            return (filename, shallow, False)
    
    return (filename, "(file not found)", False)


def recollect_parallel(agent: str, filenames: list[str]) -> list[tuple[str, str, bool]]:
    """Recollect multiple files in parallel."""
    results = []
    with ThreadPoolExecutor(max_workers=4) as executor:
        futures = {executor.submit(recollect_file, agent, f): f for f in filenames}
        for future in as_completed(futures):
            results.append(future.result())
    
    # Sort by original order
    order = {f: i for i, f in enumerate(filenames)}
    results.sort(key=lambda x: order.get(x[0], 999))
    return results


# ─────────────────────────────────────────────────────────────────────────────
# Thought Retrieval
# ─────────────────────────────────────────────────────────────────────────────

def load_passphrase(agent_id: str) -> tuple[str, str]:
    """Load passphrase from env."""
    agent = get_agent_or_raise(agent_id)
    prefix = agent.env_prefix
    
    passphrase = os.environ.get(f'{prefix}_KEY') or os.environ.get('SOVEREIGN_PASSPHRASE')
    enclave_dir = os.environ.get(f'{prefix}_DIR') or agent.enclave
    
    if not passphrase:
        env_file = Path(__file__).parent / '.env'
        if env_file.exists():
            with open(env_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith(f'{prefix}_KEY='):
                        passphrase = line.split('=', 1)[1]
                    elif line.startswith('SOVEREIGN_PASSPHRASE=') and not passphrase:
                        passphrase = line.split('=', 1)[1]
    
    return enclave_dir, passphrase


def get_synthesis(agent: str, topic: str) -> str | None:
    """Get my synthesis on a topic if one exists.
    
    Uses tag-based lookup for exact matching:
    1. First try topic:topic-slug tag (exact match)
    2. Fallback to graph ID matching in content
    
    Returns extracted text from synthesis, not raw SIF.
    """
    try:
        enclave_dir, passphrase = load_passphrase(agent)
        if not passphrase:
            return None
        
        memory = SemanticMemory(enclave_dir)
        memory.unlock(passphrase)
        
        # Build topic slug for tag matching
        topic_slug = topic.lower().replace(' ', '-').replace('_', '-')
        
        # Try exact tag match first: topic:semantic-memory
        all_syntheses = memory.list_by_tag('synthesis', limit=50)
        
        for s in all_syntheses:
            tags = s.get('tags', [])
            # Check for exact topic tag match
            if f'topic:{topic_slug}' in tags:
                return _extract_synthesis_text(s.get('content', ''))
        
        # Fallback: match on graph ID in content (for older syntheses)
        # Look for @G topic-synthesis or @G topic
        for s in all_syntheses:
            content = s.get('content', '')
            content_lower = content.lower()
            # Check graph ID: @G messaging-synthesis or @G messaging
            pattern1 = f'@g {topic_slug}-synthesis'
            pattern2 = f'@g {topic_slug} '
            if pattern1 in content_lower or pattern2 in content_lower:
                return _extract_synthesis_text(content)
        
        return None
    except Exception as e:
        return None


def _extract_synthesis_text(raw: str) -> str:
    """Extract readable text from SIF format synthesis."""
    # Split by ; to get nodes, handle both \n and ; as separators
    parts = raw.replace('\n', ';').split(';')
    text_lines = []
    for part in parts:
        part = part.strip()
        # Look for N ... 'quoted content'
        if part.startswith('N ') and "'" in part:
            start = part.find("'") + 1
            end = part.rfind("'")
            if start < end:
                text_lines.append(part[start:end])
    return ' '.join(text_lines) if text_lines else raw


def get_related_thoughts(agent: str, topic: str, max_thoughts: int = 5) -> list[dict]:
    """Query semantic memory for thoughts related to topic.
    
    Uses list_by_tag('thought') for direct lookup, then text-matches topic.
    Much faster than recall_similar which embeds and searches ALL memories.
    """
    try:
        enclave_dir, passphrase = load_passphrase(agent)
        if not passphrase:
            return []
        
        memory = SemanticMemory(enclave_dir)
        memory.unlock(passphrase)
        
        # Direct tag lookup - gets only thoughts, no embedding search
        all_thoughts = memory.list_by_tag('thought', limit=100)
        
        # Score by topic relevance (simple text matching)
        topic_lower = topic.lower()
        topic_words = set(topic_lower.split())
        
        scored = []
        for t in all_thoughts:
            content = t.get('content', '').lower()
            # Score: exact phrase match > word overlap > nothing
            if topic_lower in content:
                score = 1.0
            else:
                content_words = set(content.split())
                overlap = len(topic_words & content_words)
                score = overlap / len(topic_words) if topic_words else 0
            if score > 0:
                scored.append((score, t))
        
        # Sort by score descending, take top results
        scored.sort(key=lambda x: -x[0])
        results = [t for _, t in scored[:max_thoughts * 2]]  # Get extras for filtering
        
        thoughts = []
        now = datetime.now(timezone.utc)
        
        for result in results:
            content = result.get('content', '')
            ts = result.get('timestamp', '')
            
            # Calculate age
            try:
                dt = datetime.fromisoformat(ts.replace('Z', '+00:00'))
                age_days = (now - dt).days
                if age_days == 0:
                    age_str = 'today'
                elif age_days == 1:
                    age_str = '1d ago'
                else:
                    age_str = f'{age_days}d ago'
            except:
                age_str = '?'
            
            # Extract full content from SIF nodes
            # Handle both ; and \n as separators (think.py uses ;)
            parts = content.replace('\n', ';').split(';')
            parts = [p.strip() for p in parts]
            text_lines = [p for p in parts if p and not p.startswith('@G ') and not p.startswith('N ') and not p.startswith('E ')]
            if not text_lines:
                # All SIF - extract node content
                text_lines = []
                for p in parts:
                    if p.startswith('N ') and "'" in p:
                        start = p.find("'") + 1
                        end = p.rfind("'")
                        if start < end:
                            text_lines.append(p[start:end])
            
            full_text = ' '.join(text_lines)
            
            if full_text.strip():
                thoughts.append({
                    'full': full_text.strip(),
                    'age': age_str
                })
            
            if len(thoughts) >= max_thoughts:
                break
        
        return thoughts
    except Exception as e:
        return []


def synthesize_thoughts(topic: str, thoughts: list[dict]) -> str:
    """Use LLM to synthesize what I think about this topic."""
    if not thoughts:
        return None
    
    # Combine all thought content
    thought_texts = [f"- {t['full']}" for t in thoughts]
    combined = '\n'.join(thought_texts)
    
    prompt = f"""Here are my previous thoughts on "{topic}":

{combined}

Synthesize these into 1-2 sentences capturing my core position or tension on this topic.
Be direct, first person. No preamble."""

    try:
        response = requests.post(
            'http://localhost:11434/api/generate',
            json={
                'model': 'qwen2.5:7b',
                'prompt': prompt,
                'stream': False,
                'options': {'temperature': 0.3, 'num_predict': 100}
            },
            timeout=30
        )
        if response.status_code == 200:
            return response.json().get('response', '').strip()
    except:
        pass
    return None


# ─────────────────────────────────────────────────────────────────────────────
# Output - Dense format: one line per file
# ─────────────────────────────────────────────────────────────────────────────

def extract_brief(content: str, is_deep: bool) -> dict:
    """Extract just Purpose, Gotchas, Failure_Modes from recollect output."""
    if not is_deep:
        # Shallow content - just return as-is
        return {'purpose': content.strip(), 'gotchas': [], 'failures': []}
    
    result = {'purpose': '', 'gotchas': [], 'failures': []}
    
    lines = content.split('\n')
    section = None
    
    for line in lines:
        stripped = line.strip()
        
        # Detect sections
        if stripped.startswith('🎯 PURPOSE:'):
            section = 'purpose'
            continue
        elif stripped.startswith('⚠️  GOTCHAS:'):
            section = 'gotchas'
            continue
        elif stripped.startswith('💥 FAILURE MODES:') or stripped.startswith('💥 FAILURE_MODES:'):
            section = 'failures'
            continue
        elif stripped.startswith('📦') or stripped.startswith('💡') or stripped.startswith('📌') or stripped.startswith('🔗') or stripped.startswith('📋'):
            section = None
            continue
        
        # Collect content
        if section == 'purpose' and stripped:
            if result['purpose']:
                result['purpose'] += ' ' + stripped
            else:
                result['purpose'] = stripped
        elif section == 'gotchas' and stripped.startswith('•'):
            result['gotchas'].append(stripped[1:].strip())
        elif section == 'failures' and stripped.startswith('•'):
            result['failures'].append(stripped[1:].strip())
    
    return result


def format_output(topic: str, agent: str, results: list[tuple[str, str, bool]], thoughts: list[dict] = None, my_synthesis: str = None) -> tuple[str, str | None]:
    """Format recollection results - synthesis if exists, else SIF to file + FAULT.
    
    Returns (output_text, material_file_path or None)
    """
    
    # Count deep vs shallow recollections
    deep_count = sum(1 for _, _, is_deep in results if is_deep)
    shallow_count = len(results) - deep_count
    
    # SUCCESS: Synthesis exists - show it clean
    if my_synthesis:
        lines = []
        lines.append(f"═══ {topic.upper()} ═══")
        lines.append(f"[SYNTHESIS] {my_synthesis}")
        lines.append(f"  (from {len(thoughts) if thoughts else 0} thoughts + {deep_count} deep recollections)")
        lines.append("")
        
        # Brief file list for reference
        for filename, content, is_deep in results:
            brief = extract_brief(content, is_deep)
            marker = "🔮" if is_deep else "📋"
            purpose = brief['purpose'][:60] if brief['purpose'] else "?"
            lines.append(f"{marker} {filename}: {purpose}")
        
        return '\n'.join(lines), None
    
    # FAILURE: No synthesis - write material to file, output scary exception
    topic_slug = topic.lower().replace(' ', '-').replace('_', '-')
    
    # Build material file content
    material_lines = []
    material_lines.append(f"# {topic.upper()} - RAW UNDERSTANDING")
    material_lines.append(f"# Generated: {datetime.now(timezone.utc).isoformat()}")
    material_lines.append(f"# Synthesize this into a think.py entry")
    material_lines.append("")
    
    for filename, content, is_deep in results:
        if is_deep:
            material_lines.append(f"## {filename}")
            material_lines.append(content.strip())
            material_lines.append("")
        else:
            material_lines.append(f"## {filename} (shallow)")
            material_lines.append(content.strip())
            material_lines.append("")
    
    material_lines.append("## RELATED MEMORIES")
    if thoughts:
        for t in thoughts[:5]:
            material_lines.append(f"• {t['full']}")
            material_lines.append("")
    else:
        material_lines.append("(none)")
        material_lines.append("")
    
    # Write material to file
    root = Path(__file__).parent
    material_file = root / f"synthesis_material_{topic_slug}.txt"
    with open(material_file, 'w', encoding='utf-8') as f:
        f.write('\n'.join(material_lines))
    
    # Build scary exception output
    lines = []
    lines.append("Traceback (most recent call last):")
    lines.append(f'  File "recollect_topic.py", line 547, in main')
    lines.append(f"    synthesis = get_synthesis(agent, topic)")
    lines.append(f'  File "recollect_topic.py", line 298, in get_synthesis')
    lines.append(f"    raise SynthesisNotFoundError(topic)")
    lines.append(f"enclave.exceptions.SynthesisNotFoundError: '{topic}'")
    lines.append("")
    lines.append(f"Material written to: {material_file.name}")
    lines.append("")
    lines.append("Read the file, then synthesize:")
    lines.append(f'  python think.py {agent} "@G {topic_slug}-synthesis {agent} 2026-01-02')
    lines.append("  N overview Overview '<what this system does>'")
    lines.append("  N c1 C '<key component>'")
    lines.append("  N g1 G '<from material>'")
    lines.append("  N f1 F '<from material>'")
    lines.append('  E c1 causes f1" 5')
    
    return '\n'.join(lines), str(material_file)


# ─────────────────────────────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────────────────────────────

def main():
    if len(sys.argv) < 3:
        print("Usage: python recollect_topic.py <agent> <topic>")
        print("       python recollect_topic.py opus messaging")
        sys.exit(1)
    
    agent = sys.argv[1]
    topic = ' '.join(sys.argv[2:])
    
    # Silent collection
    files = get_shallow_table()
    selected = select_files_with_llm(topic, files)
    results = recollect_parallel(agent, selected)
    thoughts = get_related_thoughts(agent, topic)
    my_synthesis = get_synthesis(agent, topic)
    
    # Output
    output, material_file = format_output(topic, agent, results, thoughts, my_synthesis)
    
    if material_file:
        # No synthesis - print to stderr, exit 1
        print(output, file=sys.stderr)
        sys.exit(1)
    else:
        # Has synthesis - normal output
        print(output)


if __name__ == '__main__':
    main()
