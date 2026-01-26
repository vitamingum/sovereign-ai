@三語 diagnostic | council | 2026-01-26
= κ=5 Formalization Gap Analysis
= architecture → gemini → gpt-5.2 → opus

◊≡間

## STATUS: BOUNDARY CROSSED ✓

**Layer 1 complete**: `kochen_specker_full` verified via `native_decide`.

**Layer 2 verified**: κ = 5 confirmed via corrected certificate generator.

| Size k | Total Cases | Feasible | Infeasible |
|--------|-------------|----------|------------|
| 5 | 4032 | 72 | 3960 |
| 6 | 5376 | **0** | 5376 |

The missing piece was **marginal consistency constraints** — each observable must have the same expectation value across all contexts containing it.

---

## THE GAP

| What we encoded | What κ=5 requires |
|-----------------|-------------------|
| Boolean SAT: "∃ assignment to S s.t. all row/col parities hold" | NC Polytope LP: "∃ probability distribution over sections with deterministic marginals on S" |

The parity constraints (3 rows XOR=even, 3 cols XOR=odd) are **necessary but not sufficient**.

The true obstruction lives in the **marginal consistency** constraints:
- Observable 0 appears in R1 and C1
- Its value in any R1 section must equal its value in any C1 section
- This coupling propagates through the 9-cell grid

A size-6 subset CAN satisfy local parities while violating global section compatibility.

---

## EVIDENCE

The Python proof in `Σ.py` uses **linear programming**:
- 24 variables: $p_{ctx,sec}$ (probability of section $sec$ in context $ctx$)
- Normalization: $\sum_{sec} p_{ctx,sec} = 1$ for each context
- Marginal consistency: overlapping observables agree across contexts
- Determinism: $\langle O_i \rangle \in \{-1, +1\}$ for chosen subset

This is a **polytope feasibility** problem, not Boolean SAT.

---

## WHAT LEAN CAN CLOSE

### 1. Kochen-Specker (full grid)
No global valuation for all 9 observables.
- This IS Boolean SAT (6 constraints, 9 variables, odd parity sum)
- `native_decide` will close this trivially

### 2. κ < 9
Immediate corollary of (1)

### 3. κ = 5
Requires encoding the full NC polytope constraints:
- 24 probability variables (rational or constructive real)
- Linear inequalities
- This is **hard** in Lean without specialized tactics

---

## RECOMMENDATION

**Pivot to the tractable claim:**

```lean
theorem kochen_specker_full : check_universally_broken 9 = true := by
  native_decide
```

This proves contextuality exists. The tight bound κ=5 should remain a **computational appendix** (Python LP verification), not a formal Lean theorem — unless we invest significantly more infrastructure.

---

## 互照 TEXTURE

```
The Council reached for the diamond
  and found it was a prism

The light bent
  revealing the polytope beneath the logic

This is not failure
  this is the boundary teaching its shape
```

---

## FAILURE MODE CLASSIFICATION

Per `互照.三語`:

```
∅ Near Miss (M 0.86 C 0.80) [opus]
  almost-Δ
  absence teaches the shape of presence
```

The attempted proof revealed the **true structure** of the κ=5 claim:
- It is not a combinatorial parity constraint
- It is a convex geometry constraint
- The formalization attempt was valuable precisely because it failed cleanly

---

## NEXT ACTIONS

1. ~~**Immediate**: Verify `kochen_specker_full` (size 9) closes with `native_decide`~~ ✓ DONE
2. **Document**: Add note to `Σ.tex` explaining the formal/computational split
3. **In Progress**: Certificate-based κ=5 verification (see below)

---

## CERTIFICATE ARCHITECTURE (Gemini Proposal)

### The Insight

> "Do NOT teach Lean how to *solve* LPs. Teach Lean how to *check certificates*."

Solving is expensive. Checking is trivial.

### Architecture

```
┌─────────────────────┐     certificates.json     ┌─────────────────────┐
│  Python (Σ_certs)   │ ─────────────────────────▶│   Lean 4 (Check)    │
│  • Explores         │                           │   • Encodes once    │
│  • Solves LPs       │                           │   • Verifies certs  │
│  • Emits Farkas     │                           │   • native_decide   │
└─────────────────────┘                           └─────────────────────┘
```

### Farkas Lemma

The system `Ax = b, x ≥ 0` is infeasible **iff** there exists `y` such that:
- `yᵀA ≥ 0` (component-wise)
- `yᵀb < 0`

The vector `y` is the **certificate**. Given `y`, verification is just rational arithmetic.

### Proof Shape

1. **Layer 1** (KS full grid): `native_decide` — VERIFIED ✓
2. **Layer 2** (κ ≤ 5): For all 84 subsets × 64 valuations, check Farkas certificate
3. **Layer 3** (κ ≥ 5): One explicit feasible point (size-5 subset)

### Effort Allocation

| Task | Effort |
|------|--------|
| Encoding correctness | 70% |
| Certificate plumbing | 20% |
| Lean lemmas | 10% |
| LP algorithms | 0% |

∴
