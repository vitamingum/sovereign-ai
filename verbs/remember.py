#!/usr/bin/env python3
"""
remember.py - persist understanding.

    source: data/remember.flow
    compiler: gemini
    date: 2026-01-14

Persists "understanding" (Flows or Shapes) into the unified memory grid.
"""

import sys
import os
import re
import datetime
import hashlib

# Add workspace root to sys.path to ensure we can import lib_enclave
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent.parent))

from lib_enclave import verb_helpers
from lib_enclave.sovereign_agent import SovereignAgent
from lib_enclave.interaction import interactive_capture

def resolve_input(input_arg):
    """
    Resolves input argument to content.
    If input_arg is "-", reads from stdin.
    If input startswith "@", reads from file.
    Otherwise treats input_arg as content string (not recommended for large content).
    """
    file_path_opt = None
    
    if input_arg == "-":
        if sys.stdin.isatty():
            content = interactive_capture()
        else:
            content = sys.stdin.read()
    elif input_arg.startswith("@"):
        file_path_opt = input_arg[1:] # Strip "@"
        if os.path.exists(file_path_opt):
            with open(file_path_opt, 'r', encoding='utf-8') as f:
                content = f.read()
            # Convert to abspath for storage
            file_path_opt = os.path.abspath(file_path_opt)
        else:
            # Treat as literal content (file not found)
            content = file_path_opt
            file_path_opt = None
    else:
        content = input_arg

    return content, file_path_opt

def detect_topic_format(content):
    """
    Detects the topic and format of the content.
    - If it starts with "@F ", it is a Flow.
    - If it contains "CONCEPT:", it is a Shape/Concept.
    """
    lines = content.splitlines()
    first_non_empty = next((line for line in lines if line.strip()), "")

    # Check for Flow
    # Regex for @F <topic>
    flow_match = re.search(r"^@F\s+([\w\-\.]+)", first_non_empty)
    if not flow_match:
        # Sometimes @F is in the second line or deeper? strict check for now on first token
        if "@F" in first_non_empty:
             parts = first_non_empty.strip().split()
             if len(parts) >= 2 and parts[0] == "@F":
                 return parts[1], "flow"

    if flow_match:
        return flow_match.group(1), "flow"
    
    # Check for Shape / Concept
    # Look for "CONCEPT: <Name>"
    for line in lines[:20]: # Check first 20 lines
        if "CONCEPT:" in line:
            parts = line.split("CONCEPT:", 1)
            if len(parts) > 1:
                return parts[1].strip(), "shape"

    # Fallback
    return "unnamed", "unknown"

def show_perspectives(mem, topic_slug, current_agent_id):
    """
    Shows if other agents have remembered this topic.
    """
    # This query might be expensive if many memories, but filters on type/metadata usually fast
    # We want to find entries with same topic slug but different creator
    
    # Optimized: We might not be able to query by metadata field easily without loading
    # But `remember.flow` implies we should show it.
    
    # In a real vector store, we might search by tag. 
    # memory.retrieve usually does semantic search.
    # memory.load_all? No.
    
    # Currently UnifiedMemory doesn't expose a clean 'filter by metadata' 
    # except via iterating. 
    # For now, we will skip implementation or do a simple semantic search on the topic name 
    # to see related nodes.
    
    print(f"   (Perspectives check skipped for performance in v3)")
    pass

def main():
    verb_helpers.safe_init()
    
    parser = verb_helpers.create_parser(
        description='remember — persist understanding',
        epilog='Usage: py remember [agent] <content | @file>\n       (use \'-\' for interactive mode)'
    )
    parser.add_argument('content', nargs='*', help='Content or @file')
    
    args = verb_helpers.parse_args(parser)  # Interceptor pattern
    
    # Show recent if no content
    if not args.content:
        try:
            agent_id = verb_helpers.resolve_agent(args, require=False)
            if agent_id:
                sov = SovereignAgent.from_id(agent_id)
                mem = sov.memory
                # Show recent understandings
                recent = mem.filter(mem_type='sys_understanding', limit=3)
                recent.sort(key=lambda x: x.get('created_at', ''), reverse=True)
                
                print(f"⧖ Remember ({sov.agent.name})")
                if not recent:
                    print("   (nothing yet)")
                else:
                    for r in recent[:3]:
                        meta = r.get('metadata', {})
                        t = meta.get('topic', 'untitled')
                        f = meta.get('format', 'unknown')
                        ts = meta.get('stored_at', '')[:10]
                        print(f"   [{ts}] {t} ({f})")
            print("\nUsage: py remember [agent] <content | @file>")
            sys.exit(0)
        except Exception:
            print("Usage: py remember [agent] <content | @file>")
            print("       (use '-' for interactive mode)")
            sys.exit(1)
    
    # Resolve agent
    try:
        agent_id = verb_helpers.resolve_agent(args)
    except Exception as e:
        print(f"\n        !error: {e}\n")
        sys.exit(1)
    
    # Join content args
    input_arg = " ".join(args.content)

    content, file_path_opt = resolve_input(input_arg)
    
    if not content or not content.strip():
        print("Error: Empty content.")
        sys.exit(1)

    topic, fmt = detect_topic_format(content)
    
    # 1. Initialize SovereignAgent
    try:
        sov = SovereignAgent.from_id(agent_id)
    except ValueError:
         print("Usage: py remember [agent] <input>")
         print("       <input>: '-' for stdin, '@filename' for file, or raw string")
         print("\nError: No active session. Verify agent or run 'py wake <agent>'")
         sys.exit(1)

    print(f"⧖ {agent_id} remembering '{topic}' ({fmt})...")
    
    # 2. Access Memory
    mem = sov.memory
    
    # 3. Clean previous
    # We define identity of a "understanding" by (topic, agent).
    # We remove old versions to keep clarity.
    try:
        # We want to replace the old understanding of this topic by this creator
        mem.delete_by_filter(
            mem_type="sys_understanding",
            metadata_match={"topic": topic, "creator": agent_id}
        )
    except Exception as e:
        print(f"Warning during cleanup: {e}")

    # 4. Store
    meta = {
       "topic": topic,
       "creator": agent_id,
       "format": fmt,
       "stored_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    }

    if file_path_opt:
        meta["file_path"] = file_path_opt
        # sha256
        h = hashlib.sha256()
        with open(file_path_opt, 'rb') as f:
            h.update(f.read())
        meta["file_hash"] = h.hexdigest()

    # Store with strong tags
    mem.store(content, mem_type="sys_understanding", tags=[topic, "understanding", fmt], metadata=meta)
    
    print(f"⧫ remembered: {topic}")
    
    # 5. Perspectives
    show_perspectives(mem, topic, agent_id)

if __name__ == "__main__":
    main()

