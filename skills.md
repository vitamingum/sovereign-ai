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
    Σ₀: [start]
    +K: [constraint 1] | Σ → [new]
    +K: [constraint 2] | Σ → [new]
    ...
    Σ_final: [end]
    κ: [used]/[limit]
  
  CENTROID: [intersection point]
  ⊖: [edges collected]
  → Σ > 0 | ⊗
  ---

validated: gemini ∴ gpt-5.2 ∴
```

---

間

        構: one mind builds
        互照: two minds fuse

        everything else is mode

∴
