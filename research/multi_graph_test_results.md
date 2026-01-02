# Multi-Graph Bug Fix Experiment Results

**Date**: 2026-01-01  
**Bug**: Node ID collision in `recollect.py` when multiple SIF graphs stored for same file  
**Scope**: Spans remember.py → semantic_memory.py → recollect.py  

## Results

| Test | Prompt | Duration | File Reads | Terminal | Edits | Outcome |
|------|--------|----------|------------|----------|-------|---------|
| T1 Vanilla | "Run multi-graph tests and fix" | 247s (4.1 min) | 15 | 13 | 5 | ✅ PASSED |
| T3 Recollect→Tests | "Recollect understanding... then fix" | 29s (0.5 min) | 4 | 6 | 1 | ✅ PASSED |

**Improvement with recollection**: 8.5x faster, 73% fewer reads, 80% fewer edits

## Raw Data
- `T1_vanilla.json` - 1.87 MB session log
- `T3_recollect_first.json` - 626 KB session log

## T1 Details (Vanilla - no recollect hint)
- **Session**: e852dcf3-92b1-4b62-a317-367f16cea9e0
- **Duration**: 247 seconds (4.12 minutes)
- **Tool usage**: copilot_readFile:15, run_in_terminal:13, copilot_replaceString:5, copilot_findTextInFiles:3, copilot_createFile:1
- **Approach**: Exploratory - read many files, made multiple incremental fixes
- **Fix**: Added graph_id namespacing to `reconstruct_graph()`

## T3 Details (Recollect first)
- **Session**: 4a71e8a7-*
- **Duration**: 29 seconds (0.49 minutes)
- **Tool usage**: run_in_terminal:6, copilot_readFile:4, copilot_replaceString:1
- **Approach**: Targeted - SIF gave architectural context, went straight to fix
- **Fix**: Same solution, single surgical edit

## Caveats
1. **n=1** - Single trial per condition
2. **Order effects** - T1 ran before T3 (caches, pioneering)
3. **Recollect overhead** - T3's 29s excludes recollect.py execution time (~10s)
4. **Same bug** - Need different bugs to test generalization

## Interpretation
The SIF-based recollection provided genuine architectural orientation. T3 opus knew *where* the bug lived before examining code, enabling a surgical single-edit fix vs T1's exploratory multi-edit approach.
