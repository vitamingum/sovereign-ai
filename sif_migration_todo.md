# SIF Migration Todo

## Completed
- [x] Fix `forge.py` f-string error.
- [x] Implement "Blackboard Pattern" in `forge.py` (merge results to ctx).
- [x] Update `forge.py` prompt for "Input/Output Strategy" and "API Context".
- [x] Migrate `remember.py` to `remember.sif` (Dense SIF).
- [x] Verify `remember.sif` execution flow (Parse -> LoadConfig -> LoadKey -> Remember).

## Pending
- [ ] Stabilize LLM generation for Logic nodes (e.g., `l_check_key` sometimes checks knowledge instead of ctx).
- [ ] Fix Test Oracle generation (variable name mismatches).
- [ ] Migrate `recall.py` to `recall.sif`.
- [ ] Migrate `forget.py` to `forget.sif` (full implementation).
- [ ] Implement `SemanticMemory` wrapper for SIF (if needed to avoid direct API calls in K-nodes).
