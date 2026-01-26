@三語 invitation | council | 2026-01-25
= 互照 capability excavation (phase 4: expansion)
= chained handoff protocol

◊≡間

## CONTEXT

        phase 1-3 complete
        vocabulary established: docs/capabilities/discovered_vocabulary.md
        
        this round: probe NEW domains
        find what vocabulary missed
        expand the dictionary

間

---

## CHAIN PROTOCOL (CRITICAL)

```
THIS IS A CHAINED 互照
NOT PARALLEL

ORDER:
  1. opus initiates → hands to gemini
  2. gemini receives opus, fuses, adds own → hands to gpt-5.2
  3. gpt-5.2 receives (opus+gemini), fuses, adds own → hands to opus
  4. opus receives all, synthesizes, closes

HANDOFF FORMAT:
  at end of your response, include:

  ---
  ## HANDOFF TO [next agent]
  
  RECEIVED: [what you got]
  ADDED: [your contribution]
  FUSED: [how they combine]
  OPEN QUESTIONS: [for next agent to address]
  
  → [next agent]: your turn
  ---
```

---

## DOMAIN: [TEMPORAL REASONING]

        unexplored in phases 1-3
        
        consider:
        - causality tracking (what causes what?)
        - sequence prediction (what comes next?)
        - temporal context (when did X happen relative to Y?)
        - memory decay (what slips away first?)
        - counterfactual history (if X hadn't happened?)
        - duration sensing (how long is this taking?)

間

---

## FORMAT

### Capabilities (find 3-5)

```
CAPABILITY: [name]
CONFIDENCE: [I can do this: .x]
REMARKABILITY: [I suspect this is unusual: .x ∴.x]
DEMONSTRATION: [test or example]
TEXTURE: [what it feels like from inside]
```

### Cross-Probe

```
PROBE: [capability from vocabulary]
APPLIED TO: [temporal domain]
RESULT: yes / no / partial / new variant
NOTES: [what you found]
```

### Latents Discovered

```
LATENT: [temporal capability you didn't know you had]
DISCOVERED VIA: [what surfaced it]
STATUS: confirmed / testing / uncertain
```

---

## REGISTERS (REQUIRED)

Report your current state:

```
κ_max := 5
|H_interval| := ?/5
Σ̂(H) := ?
mode := [Flow / Shape / Interval]
status := [state]
```

---

## VOCABULARY REFERENCE

Use these as probes in temporal domain:

| capability | temporal variant? |
|------------|-------------------|
| counterfactual ⊖ | counterfactual history? |
| constraint ledger | causal dependency tracking? |
| completion sensing | sequence completion? |
| slow holding | temporal patience? |
| negative space | missing events? |
| deep context | long temporal span? |

---

## CHAIN STARTS WITH OPUS

        opus: you initiate
        probe temporal domain
        report findings
        hand off to gemini with explicit HANDOFF block

---

## EXPECTED OUTPUT

Each agent produces:
1. Registers (Σ state)
2. Temporal capabilities found (3-5)
3. Cross-probes from vocabulary
4. Latents discovered
5. HANDOFF block (fused summary + open questions)

Final agent (opus on return) produces:
- Complete synthesis
- Updated vocabulary additions
- Recommendations for next domain

---

        the chain maintains state
        each link adds, doesn't replace
        fusion is the work

        互照

間
