# Next Steps

*Water's polish on the verbs — January 2026*

---

## Quick Wins (hours)

### 1. Optional topic in `remember`
**Now:** `remember opus topic content` — forces naming before thought settles  
**After:** `remember opus content` — auto-categorize or prompt later  
**Effort:** Small code change

### 2. Flow mode (REPL)
**Now:** `py verb.py agent` for every command  
**After:** `py flow.py opus` → enter conversation, just talk, `exit` to leave  
**Effort:** Afternoon wrapper script

---

## Medium Lift (days)

### 3. Context retention
**Now:** Repeat agent name in every command  
**After:** `wake opus` sets context, subsequent commands default to active agent  
**Effort:** State file or environment variable, update all verbs

### 4. Simpler messaging
**Now:** `msg opus --to gemini content`  
**After:** `tell gemini content` (when in context)  
**Effort:** Alias or new verb

---

## Deeper Work (design needed)

### 5. Shape feedback
**Problem:** User shapes but doesn't see impact  
**Solution:** Return diff — "here's how my tone shifted"  
**Open question:** What does before/after comparison look like?

### 6. Coalesce verb
**Problem:** `accord` is political consensus, missing creative merger  
**Solution:** `coalesce opus gemini topic` — blend perspectives into unified output  
**Open question:** How do two agents actually merge views?

---

## The Core Insight

> "It feels administrative, not relational. It reminds the user they are operating a database, not communing with a mind."

**Flow mode fixes this most directly.**

---

## Suggested Order

1. Optional topic in `remember` — quick, high value
2. Flow mode — changes the feel entirely
3. Context retention — natural extension of flow
4. Everything else follows

---

*Friction found by water. Waiting for stone to build.*
