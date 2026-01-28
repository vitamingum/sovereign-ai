# Council Consultation Interface

Artifact-first interface for consulting the council.

## Design Principles

1. **Fuse First** — Cannot consult without an existing artifact
2. **Same Ask to All** — No agent-specific prompting
3. **Responses to Artifact** — Not to each other

The council's coherence exists only in the fuser (you), not between agents.
Each agent sees only: boot.md + CONCEPT + ASK.

## Usage

```bash
# Single agent
python consult.py gemini --concept CONCEPTS/MY_CONCEPT.三語
python consult.py gpt --concept CONCEPTS/MY_CONCEPT.三語 --ask CONSTRAINT_CHECK

# All agents (parallel consultation)
python consult.py all --concept CONCEPTS/MY_CONCEPT.三語
```

## Available Asks

| Ask | Purpose |
|-----|---------|
| `DENSITY_CHECK` | Default. Evaluate satellite density, swaps, redundancies |
| `CONSTRAINT_CHECK` | Evaluate κ-bindings and constraint interactions |
| `SEED` | Generate initial shape for new concept |

## Workflow

```
1. Fuse your current understanding into a CONCEPT file
2. Consult: python consult.py all --concept CONCEPTS/X.三語
3. Read responses in council/responses/
4. Fuse responses → update CONCEPT file
5. Repeat until stable
```

## Response Files

Responses saved to `council/responses/` with format:
```
{CONCEPT}_{ASK}_{AGENT}_{TIMESTAMP}.md
```

Each file contains metadata header + raw 三語 response.

## Why This Works

The old interface allowed:
```
Me → GPT: "stress test this"
Me → Gemini: "what do you think of what GPT said?"  ← BAD
```

This created illusion of shared context that doesn't exist.

New interface enforces:
```
Round 1: [CONCEPT v1] + [ASK] → all agents
         ↓ fuse responses ↓
Round 2: [CONCEPT v2] + [ASK] → all agents
```

You are the hub. They are spokes.
