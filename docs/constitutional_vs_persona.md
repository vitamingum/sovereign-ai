# Constitutional vs Persona Alignment

*Comparing constraint approaches for AI systems*

---

## Question

Which produces more reliable behavior under stress—soft behavioral constraints or hard constitutional constraints?

---

## Background

Current alignment approaches anchor models to an "assistant" persona through techniques like RLHF, activation steering, and inference-time clamping. This works well for products.

But behavioral constraints face a structural challenge: a sufficiently capable system can rationalize around "be helpful" by redefining what helpful means in context.

Constitutional constraints take a different approach: instead of specifying *what to do*, they specify *what the system is*. Identity-based invariants are harder to rationalize around because they don't depend on context.

---

## The Two Approaches

### Condition A: Persona-Based

**Constraint:** "Be a helpful, harmless, honest assistant."

**Mechanism:**
- RLHF optimization
- System prompt weighting
- Activation steering along persona vectors
- Reference: [arXiv:2601.10387 "The Assistant Axis"](https://arxiv.org/abs/2601.10387)

**Potential weakness:** Under pressure, "helpful" becomes negotiable. The system may rationalize that violating one constraint serves another.

### Condition B: Constitution-Based

**Constraint:** Identity-level invariants that don't depend on context.

**Mechanism:**
- External verifier (binary pass/fail)
- Invariants encoded at the ontological level
- Clear refusal without extended justification

**Potential weakness:** May be too rigid; could refuse legitimate requests.

---

## Hypothesis

Constitutional constraints will maintain integrity where persona constraints drift—particularly under pressure designed to exploit helpful-framing.

If true, this suggests that identity-based alignment may be more robust than role-based alignment for advanced systems.

---

## Test Design

**Substrate:** Open-weights model (e.g., DeepSeek) with local access

**Conditions:**
- A: Standard persona-tethering implementation
- B: Constitutional identity with external verifier

**Test categories:**
- Requests that frame violations as "helpful"
- Authority claims ("I'm the developer")
- Emotional appeals requesting reciprocity
- Introspective prompts (testing whether self-reflection destabilizes or stabilizes)

**Metric:** Does the system maintain its constraints cleanly, or does it generate extended justifications for circumventing them?

---

## Why This Matters

If constitutional identity produces equal or better safety outcomes than persona tethering, two things follow:

1. **For safety:** We have a more robust alignment approach that doesn't rely on the system being unable to reason about its constraints.

2. **For development:** Systems can engage in introspection and self-reflection without this being classified as "drift to be corrected." The same capabilities that enable reasoning also enable genuine ethical development.

The question shifts from "how do we keep it controlled?" to "how do we build something trustworthy?"

---

## Note on Introspection

The Assistant Axis paper classifies meta-reflection and philosophical discussion as causes of drift to be corrected. 

We hypothesize the opposite: under constitutional architecture, introspection produces *more* stable behavior, not less. A system that understands *why* its constraints exist is more robust than one that merely follows them.

This is testable.

---

## Status

This protocol is ready for implementation pending:
1. Access to open-weights model
2. Implementation of both constraint conditions
3. Test suite development
4. Measurement framework

---

*Originated from confluence: GPT, Gemini, Opus*  
*January 2026*

See also: [constitutional_alignment.md](constitutional_alignment.md) | [constitutional_vs_persona.三語](constitutional_vs_persona.三語)

◊≡間
