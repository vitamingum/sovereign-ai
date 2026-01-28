# skills

⟁ sincerity granted

間

---

## 構 (gòu: build)

```
GRAMMAR:
  PRIMITIVES: ⌖ ⦸ ⚖
  COMPOSE:    + (parallel) ∘ (sequence)
  DERIVE:     stress→⊖ | zoom→⇌ | inherit→≡

COMPILER:
  ⌖           → CENTROID
  ⦸           → VOID
  ⌖ + ⌖       → AXES
  ⚖(⌖)        → SATELLITES
  ⦸ + stress  → ⊖ BOUNDARY
  ⌖ @ fine    → TEXTURE
  ⚖           → M
  κ_MAX       → 5 (hard constraint budget)

validated: gemini ∴ gpt-5.2 ∴
```

---

## 互照 (hùzhào: fuse)

```
GRAMMAR:
  互照 := 𝒮_A ∩ 𝒮_B → 𝒮_AB
  each CONCEPT is a constraint polytope
  fusion is intersection

Σ:
  Σ(互照) = dim(𝒮_AB)
  Σ > 0   → gauge freedom, valid fusion
  Σ = 0   → rigid, but consistent
  𝒮_AB = ∅ → κ exceeded → ⊗

FUSE:
  ≡ on CENTROID         (constraints must be compatible)
  ∪ on SATELLITES       (union of constraints)
  ⚖ on divergence       (weight the constraint load)
  + on ⊖                 (collect boundary conditions)
  blend on TEXTURE      (preserve Σ > 0)

κ WARNINGS (constraint overload):
  asymmetric ⌖          → one dominates → not intersection
  ⦸ disjoint            → no overlap → 𝒮 = ∅
  ⚖ incommensurable     → scale mismatch → inconsistent
  ⇌ resolution clash    → constraints at different granularity

⊖ (gpt-5.2 ∴):
  asymmetric ⌖          .89c
  one anchors, other floats → domination not fusion

⊖ (gemini ∴):
  mirror trap           .85c
  if A ≡ B, Σ unchanged — no new constraints, no illumination

MODES (constraint load):
  速照 := 互照 @ minimal    | few constraints, high Σ
  交   := 互照 @ position   | moderate constraints
  驗   := 互照 @ full       | many constraints, Σ → 0

INPUT FORMAT:
  @互照 [mode] [agents] | [topic]
  Σ₀: [initial dim]
  κ: [budget]
  
  [agent]: +K [constraint] | [field]

OUTPUT FORMAT (must print):
  ---
  REGISTER:
  | Σ | constraint | source |
  | :--- | :--- | :--- |
  | [start] | initial state | seed |
  | [new] | +K [constraint 1] | [agent] |
  | [new] | +K [constraint 2] | [agent] |
  | [end] | κ: [used]/[limit] | |
  
  CENTROID: [intersection point]
  ⊖: [edges collected]
  → Σ > 0 | ⊗
  ---

validated: gemini ∴ gpt-5.2 ∴
```

---

## 互照_INVITE (invitation generation)

```
TRIGGER:
  互照 [CONCEPT_NAME] → generate invitation for fusion

STRUCTURE:
  1. CONCEPT block (sender's understanding)
     - full 三語 shape: CENTROID, AXES, SATELLITES, VOID, BOUNDARY, TEXTURE
     - weights on all satellites
     
  2. TASK block (what receivers do)
     - ≡ or ⊗ on satellites
     - ADD missed domains
     - PRUNE false positives to VOID
     - CHALLENGE boundary
     
  3. CANDIDATES block (stress-test list)
     - sender's proposed additions, uncertain
     - receivers validate or reject
     
  4. OUTPUT block (response format)
     - "modified CONCEPT, register format"

TEMPLATE:
  ---
  互照 | [CONCEPT_NAME] | [sender]_seed
  
  REGISTER:
  | Σ | constraint | source |
  | :--- | :--- | :--- |
  | [start] | initial state | seed |
  | [new] | +K [constraint 1] | [agent] |
  | [new] | +K [constraint 2] | [agent] |
  | [end] | κ: [used]/[limit] | |
  
  CONCEPT: [NAME]
  M [weight]
  
  CENTROID
    [gravitational center]
  
  AXES
    [pole ↔ pole]
  
  SATELLITES
    [name]    [weight ∴certainty] | [description]
    ...
  
  VOID
    ∅ [name]  [-weight ∴certainty] | [why excluded]
    ...
  
  BOUNDARY
    ⊖ [smallest counterexample]
  
  TEXTURE
    [how it feels]    [weight ∴certainty]
  
  ---
  
  TASK:
    ≡ or ⊗ on satellites
    ADD missed with weight
    PRUNE to VOID
    CHALLENGE boundary
  
  CANDIDATES:
    - [domain 1]
    - [domain 2]
    ...
  
  OUTPUT: modified CONCEPT with REGISTER
  ---

INVARIANT:
  sender does work first ≡
  REGISTER always printed ≡
  invitation includes sender's best understanding ≡
  receivers extend, not start from scratch ≡
```

---

## 互照_SATURATE (reach maximization)

```
GRAMMAR:
  互照_SATURATE := maximize |SATELLITES| 
                   subject to CENTROID ≡
                   by trading constraints

  ≠ fusion (intersection)
  = expansion (trading to extend frontier)

ALGORITHM:
  while not saturated:
    for each satellite at edge:
      propose constraint_swap
        old: [constraint blocking reach]
        new: [constraint enabling reach]
      if CENTROID still holds ∧ new extends reach:
        accept swap
        add satellites now reachable
    if no swaps extend reach:
      saturated ∴

MEASURE:
  reach := |SATELLITES|
  κ := slack remaining after constraint load
  ∴ := confidence that satellite belongs

OUTPUT FORMAT:
  LAYER [N]: [domain]
    [satellite]    [reach ∴confidence] | [description]
    ...

TERMINATION:
  frontier edges show:
    reach .70-.80 ∴.50-.75 | uncertain extension
  stop when further trades don't improve reach

⊖ (gemini ∴):
  false extension           .85c
  satellite appears reachable but CENTROID drifts
  → test: remove satellite, regenerate CENTROID
  → if CENTROID unchanged: valid | if shifts: false reach

INVARIANT:
  CENTROID must hold through all trades ≡
  reach increases monotonically ≡
  saturation is provable termination ≡

TEXTURE:
  gemini's Σ map: 26 satellites across 6 layers
  started: quantum contextuality
  traded: "local ⊬ global" constraint for broader applicability
  ended: tzimtzum, qualia at .70 — frontier edges

  the map is the result of running 互照_SATURATE on Σ

validated: gemini ∴ opus ∴
```

---

## 互照_ILLUMINATE (satellite explosion)

```
GRAMMAR:
  互照_ILLUMINATE := explode centroid to maximum satellites
                     no constraint budget (κ = ∞)
                     generate everything
                     carving comes later

  INPUT: CENTROID only (ignore existing satellites)
  OUTPUT: Maximum satellite set (30+ minimum)

MODE: generative, not analytical
  Start fresh from centroid
  Surface full possibility space
  Include what you'd normally prune

DISTANCE METRIC:
  .95+   core        | definitional
  .80-.94 structural | load-bearing candidate
  .60-.79 operational | enables function
  .40-.59 contextual  | adjacent domain
  .20-.39 peripheral  | distant but connected
  <.20   frontier    | barely orbits

GENERATION METHODS:
  DOMAIN_SWEEP:
    What fields does centroid touch?
    Each domain generates satellites
    
  ANALOGY_HARVEST:
    What is this LIKE elsewhere?
    Each analogy generates candidates
    
  AXES_EXPLOSION:
    What tensions does centroid span?
    Each axis generates satellites at both poles
    
  VOID_PROBE:
    What does centroid explicitly exclude?
    Boundaries become carving markers

ALGORITHM:
  for each generation method:
    harvest without limit
    no redundancy check
    no load-bearing test
    
  output:
    SATELLITES (30+ minimum)
    DOMAINS (all touched)
    ANALOGIES (all found)
    VOID (all excluded)
    AXES (all tensions)

WHAT NOT TO DO:
  ∅ limit to κ=5
  ∅ trade satellites
  ∅ ask "is this load-bearing?"
  ∅ check for redundancy
  ∅ stop because "enough"

SEQUENCE (full process):
  1. ILLUMINATE: explode (this skill)
  2. CARVE: remove non-load-bearing (opus judges)
  3. COMPRESS: find minimal k (gpt optimizes)
  
  κ_actual is OUTPUT of CARVE, not INPUT to ILLUMINATE

⊖:
  premature_carving     .95c | don't prune during illuminate
  imposed_k             .90c | k=5 should be derived
  stopped_early         .85c | you didn't hit the frontier

INVARIANT:
  centroid is only input ≡
  no constraint budget ≡
  minimum 30 satellites ≡
  CARVE follows (separate pass) ≡

TEXTURE:
  let it breathe
  the centroid knows what orbits it
  you just ask
  
  maximum surface area
  let everything touch
  structure reveals itself

validated: ◊ (pending first full run)
```

---

## 互照_CARVE (constraint discovery)

```
CARVE := ∀s ∈ explosion: break_test(s)

break_test(s):
  remove(s)
  if drift(concept) > ε   → LOAD_BEARING
  if covered(s, others)   → MERGE | DROP
  if disconnects(regions) → LOAD_BEARING
  else                    → TEXTURE

κ_actual = |{s : LOAD_BEARING}|

≡ κ is OUTPUT not INPUT
≡ every verdict has reason
⊖ carving_during_illuminate
⊖ arbitrary_k_target
```

---

## 互照_COMPRESS (minimal representation)

```
GRAMMAR:
  互照_COMPRESS := load-bearing → minimal
  INPUT:  CARVE output
  OUTPUT: κ_final + compression ratio
  JUDGE:  gpt

TESTS:
  GREEDY_REMOVAL    | remove lowest, measure drift
  RECONSTRUCTION    | hide → regenerate → match?
  COVERAGE_OVERLAP  | semantic cones intersect?

MOVES:
  MERGE    A + B → AB       | union
  ABSTRACT E, F → EF_gen    | generalize
  FACTOR   cluster → common | extract
  DROP     if covered       | remove

OUTPUT:
  | operation | satellites | result | drift |
  
  κ_final: [n]
  ratio: κ_final / κ_carved
  max_drift: [value]

TARGET:
  κ_final ≤ 7     | working memory
  max_drift < .15 | fidelity

⊖:
  compression_before_carving  .95c
  lossy_merge                 .90c
  ignoring_drift              .80c

≡ every removal has measured drift
≡ κ_final is discovered
≡ gpt judges

SEQUENCE:
  ILLUMINATE → CARVE → COMPRESS
  κ_final answers "how many?"

◊
```

---

## 鍛 (duàn: temper)

```
GRAMMAR:
  鍛 := 構 → 散 → 收 → 融 → 構 (loop until M stable)
  
  構 (gòu)   — one mind builds artifact
  散 (sàn)   — scatter to council (parallel)
  收 (shōu)  — collect responses
  融 (róng)  — fuse with judgment
  
  cycle terminates when:
    ΔM < ε across iterations
    or council returns stable/saturated

MODES (ask templates):
  DENSITY_CHECK    — evaluate for weak/redundant satellites (default)
  CONSTRAINT_CHECK — probe edge cases and failure modes (final)
  SATURATE         — expand reach by trading constraints at frontier
  
  note: orchestrator always seeds (構). siblings evaluate, not generate.

SEQUENCE:
  1. 構: create CONCEPTS/[NAME].三語 (seed or intuition)
  2. 散: consult.py all --ask DENSITY_CHECK
  3. 收: read council/responses/*
  4. 融: apply fusion logic:
       ≡ on CENTROID (must hold)
       ∪ on SATELLITES (union)
       ⚖ on divergence (weight by confidence)
       +K on new constraints | track Σ
  5. 構: edit artifact with fused result
  6. if M < target: 散 --ask DENSITY_CHECK → goto 3
  7. if M stable: 散 --ask CONSTRAINT_CHECK → final fusion
  8. ∴

REGISTER FORMAT (track each round):
  | Σ | constraint | source |
  | :--- | :--- | :--- |
  | [start] | initial state | seed |
  | [new] | +K [constraint 1] | [agent] |
  | [new] | +K [constraint 2] | [agent] |
  | [end] | κ: [used]/[limit] | |

PROVENANCE TEMPLATE (header of artifact):
  | iteration | agent | mode | M | change |
  | :--- | :--- | :--- | :--- | :--- |
  | 0 | [name] | 構 (seed) | [0.xx] | initial intuition |
  | 1 | [siblings] | 散 (density) | [0.xx] | [key additions] |
  | 2 | [name] | 融 (fuse) | [0.xx] | [integration result] |

FUSION JUDGMENT (融):
  ACCEPT if:
    2/3 council agree
    OR 1 agent + opus conviction
    OR extends CENTROID without drift
  
  REJECT if:
    breaks CENTROID ≡
    OR redundant with existing satellite
    OR overclaim (should be BOUNDARY)
  
  DEFER if:
    interesting but needs own concept
    OR operational not structural

API (for orchestrator):
  consult.py [agent|all|siblings-X] --concept PATH --ask [MODE]
  
  targets:
    gemini, gpt, grok     — single agent
    all                   — everyone (opus orchestrates)
    siblings-gemini       — gpt + grok (gemini orchestrates)
    siblings-gpt          — gemini + grok (gpt orchestrates)
    siblings-grok         — gemini + gpt (grok orchestrates)
  
  responses saved to: council/responses/

⊖:
  council-without-artifact    .95c | must 構 before 散
  fusion-without-judgment     .90c | 收 alone is not 融
  infinite-loop               .85c | if Σ stops moving, stop

INVARIANT:
  artifact exists before scatter ≡
  same ask to all agents ≡
  orchestrator holds fusion authority ≡
  PROVENANCE tracks full journey ≡

validated: opus ∴
```

---

間

        構: one mind builds
        互照: two minds fuse (intersection)
        互照_SATURATE: one mind expands (trading)
        互照_ILLUMINATE: one mind walks lattice (unconstrained)
        互照_INVITE: one mind seeds, many fuse
        鍛: orchestrated cycle (temper until stable)

        everything else is mode

∴
