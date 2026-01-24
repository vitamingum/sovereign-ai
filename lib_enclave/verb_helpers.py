"""
verb_helpers.py - Standard behaviors for all verbs.

    source: tools_architecture (2026-01-23)
    purpose: consistent invocation, unicode safety, agent resolution

            quality = (always works) × (never surprising)
"""

import sys
import argparse
from pathlib import Path
from typing import Optional

# Ensure project root in path for imports
PROJECT_ROOT = Path(__file__).parent.parent
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

# Import config (for known agents) and unicode fix
from lib_enclave.config import AGENTS
from lib_enclave.unicode_fix import fix_streams


def safe_init():
    """Ensure unicode streams are fixed before any output."""
    fix_streams()


def create_parser(description: str, epilog: str = None, include_agent_positional: bool = False) -> argparse.ArgumentParser:
    """Create parser with standard agent arguments.
    
    Args:
        description: Parser description
        epilog: Parser epilog text
        include_agent_positional: If True, adds 'agent' positional arg to argparse.
                                DEFAULT FALSE: We prefer to use parse_args() interception
                                to handle positional agents dynamically to avoid collisions.
    """
    parser = argparse.ArgumentParser(
        description=description,
        epilog=epilog,
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    
    # Flag: py verb --agent sonnet (always included)
    parser.add_argument(
        '--agent', '-a', 
        dest='agent_flag',
        help='Agent ID (flag override)'
    )
    
    # Positional (Legacy/Explicit Mode)
    if include_agent_positional:
        parser.add_argument(
            'agent', 
            nargs='?', 
            help='Agent ID (optional)'
        )
    
    return parser


def parse_args(parser: argparse.ArgumentParser) -> argparse.Namespace:
    """
    Parse arguments with Agent Interception.
    
    If the first positional argument is a known Agent ID (e.g. 'sonnet'),
    it is automatically converted to the --agent flag before parsing.
    
    This solves the 'positional collision' problem where a verb wants its own
    positional logic (e.g. recall query) but users want 'recall sonnet query'.
    """
    _intercept_agent_positional()
    return parser.parse_args()


def _intercept_agent_positional():
    """Rewrites sys.argv if the first arg is a known agent."""
    if len(sys.argv) > 1:
        # Check first arg (case-insensitive key lookup)
        potential_agent = sys.argv[1].lower()
        
        # Guard: Flags
        if potential_agent.startswith('-'):
            return

        # If it is a known agent ID
        if potential_agent in AGENTS:
            # INTERCEPT: Convert to flag
            # sys.argv is [script, agent, arg2...]
            
            # We preserve the original casing of the value
            agent_val = sys.argv[1]
            
            # Remove the positional
            sys.argv.pop(1)
            
            # Insert flag pairs
            # Result: [script, --agent, agent, arg2...]
            sys.argv.insert(1, agent_val)
            sys.argv.insert(1, '--agent')


def resolve_agent(args: argparse.Namespace, require: bool = True) -> Optional[str]:
    """
    Resolve agent ID from:
    1. Flag (--agent)
    2. Positional (agent)
    3. Session file (.sovereign_session)
    
    Side effect: Updates .sovereign_session if explicit agent found.
    """
    # 1. Flag usually overrides (explicit intent)
    if hasattr(args, 'agent_flag') and args.agent_flag:
        _update_session(args.agent_flag)
        return args.agent_flag
        
    # 2. Positional
    # Note: Ensure this isn't confusing 'content' or other positionals.
    # The parser built with create_parser guarantees 'agent' is the first positional.
    if hasattr(args, 'agent') and args.agent:
        _update_session(args.agent)
        return args.agent
        
    # 3. Session fallback
    session_file = Path(".sovereign_session")
    if session_file.exists():
        try:
            stored_id = session_file.read_text(encoding="utf-8").strip()
            if stored_id:
                return stored_id
        except Exception:
            pass
            
    if require:
        print("\n        ! error: no agent specified")
        print("        usage: py verb [agent] or py verb --agent [agent]")
        print("        (or set .sovereign_session)\n")
        sys.exit(1)
    
    return None


def _update_session(agent_id: str):
    """Update session file with active agent."""
    try:
        Path(".sovereign_session").write_text(agent_id, encoding="utf-8")
    except Exception:
        pass # Non-critical


def query_understanding(agent_id: str, topic: str) -> str:
    """
    Query sys_understanding memory for specific topic.
    
    Args:
        agent_id: Agent ID to query (uses their memory access)
        topic: Topic tag to filter by
    
    Returns:
        Content string if found, None if not found
        
    Raises:
        Exception: If agent resolution or memory access fails
    """
    from lib_enclave.sovereign_agent import SovereignAgent
    
    sov = SovereignAgent.from_id(agent_id)
    mem = sov.memory
    
    results = mem.filter(mem_type='sys_understanding', tags=[topic])
    
    if results:
        return results[0].get('content', '')
    
    return None
