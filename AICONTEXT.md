# AI Context - Shared Knowledge for All Agents

This file is read by all agents at session start. Put things here that everyone needs to know.

## Theme Sync (IMPORTANT)

Wake prints two themes that summarize this file:
- `project-architecture` - What the system IS (structure, tools, components)
- `dev-tips` - HOW to work effectively (patterns, gotchas, workflows)

**When you update AICONTEXT.md, also update the themes:**
```
py remember.py <agent> --theme project-architecture "@G ..."
py remember.py <agent> --theme dev-tips "@G ..."
```

The themes are the compressed SIF version of this doc - authoritative boot context for agents.

## Available Tools (Often Forgotten)

### Python Debugging Without Shell Escaping
Use `mcp_pylance_mcp_s_pylanceRunCodeSnippet` for running Python snippets.
- No PowerShell/bash escaping issues
- Works on Windows and Mac
- Cleaner than `python -c "..."` one-liners

Example: Instead of fighting shell quotes, just call the tool directly with your Python code.

## Project Conventions

### Memory Tools
- `recall.py <agent> <query>` - Search graphs AND journals automatically
- `remember.py <agent> <file> "@G ..."` - Store file understanding
- `remember.py <agent> --theme <topic> "@G ..."` - Store cross-file synthesis
- `journal.py <agent> "reflection"` - Private FAISS-indexed reflections
- `wake.py <agent>` - Session boot with context (prints architecture + dev-tips)
- `memory_debt.py <agent>` - Check for stale understanding

### Storage Layout
- `shared_enclave/` - Graphs, themes (SHARED_ENCLAVE_KEY)
- `enclave_<agent>/` - Private data (ENCLAVE_<AGENT>_KEY)
- Journal uses dedicated `journal_memories.jsonl` per agent
