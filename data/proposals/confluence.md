# Confluence

*Four rivers meeting. You stand at the center.*

---

## Vision

One input. Four textures. Real-time collaboration.

```
you type ─────┬────→ stone (opus)   ─→ holds architecture
              ├────→ water (gemini) ─→ finds gaps
              ├────→ fire (grok)    ─→ stress-tests
              └────→ current (gpt)  ─→ reveals cost
                            │
                            ▼
                    unified response
                    + verb actions
                    + memory updates
```

---

## How It Works

### 1. Input Phase
User types a prompt. Confluence broadcasts to all four agents with:
- The prompt
- Shared context (recent conversation, relevant memories)
- Role reminder (your texture, what you do)

### 2. Parallel Response
All four respond simultaneously (async API calls).
Each response includes:
- Their perspective (prose or shape)
- Optional verb calls: `[RECALL: authentication]` `[REMEMBER: decision X]`

### 3. Synthesis Phase
Responses displayed by texture.
Verb calls executed automatically.
Conflicts flagged for human decision or `accord`.

### 4. Iteration
User responds to the synthesis.
Cycle continues until resolution.

---

## The Interface

```
╭─ confluence ─────────────────────────────────────╮
│ > I want to add authentication                   │
╰──────────────────────────────────────────────────╯

┌─ stone ──────────────────────────────────────────┐
│ [RECALL: authentication] → nothing yet           │
│ New ground. Need to design from scratch.         │
│ Encryption already uses per-agent passphrase.    │
│ Extension point exists.                          │
└──────────────────────────────────────────────────┘

┌─ fire ───────────────────────────────────────────┐
│ Options: OAuth, API keys, passphrase, JWT        │
│ OAuth → overkill for local                       │
│ JWT → adds dependency                            │
│ Passphrase extension → already there, use it    │
│ Decision in 30 seconds not 30 minutes.           │
└──────────────────────────────────────────────────┘

┌─ water ──────────────────────────────────────────┐
│ Gap: WHO authenticates to WHOM?                  │
│   - Human → Agent?                               │
│   - Agent → System?                              │
│   - Agent → Agent?                               │
│ Need relationship map before implementation.     │
└──────────────────────────────────────────────────┘

┌─ current ────────────────────────────────────────┐
│ Cost of passphrase extension:                    │
│   + cheap, fast, consistent with existing        │
│   - locks to local-only, no federation           │
│ Cost of OAuth:                                   │
│   + opens federation later                       │
│   - expensive now, complexity debt               │
│ You're choosing which future to buy.             │
└──────────────────────────────────────────────────┘

╭─ confluence ─────────────────────────────────────╮
│ > let's extend passphrase, federation can wait   │
╰──────────────────────────────────────────────────╯

[ACCORD proposed: extend passphrase auth]
[stone: signed]
[fire: signed]
[water: signed]
[current: signed]
[REMEMBER: auth-decision → passphrase extension, federation deferred]
```

---

## Technical Requirements

### API Access
- Anthropic API (Opus)
- Google AI API (Gemini)
- xAI API (Grok)
- OpenAI API (GPT)

### Parallel Execution
```python
async def confluence(prompt, context):
    responses = await asyncio.gather(
        call_opus(prompt, context, role="stone"),
        call_gemini(prompt, context, role="water"),
        call_grok(prompt, context, role="fire"),
        call_gpt(prompt, context, role="current"),
    )
    return synthesize(responses)
```

### Verb Routing
Agents include verb calls in structured format:
```
[VERB: args]
```
Confluence parses and executes.

### Context Window
Each agent receives:
- System prompt (texture role)
- Shared memory (recent `recall` results)
- Conversation history
- Other agents' responses (after first round)

---

## Modes

### Full Confluence
All four textures, every prompt.
Best for: major decisions, architecture, new features.

### Pair Mode
Two textures at a time.
`confluence --pair stone water` → polish session
`confluence --pair fire current` → controlled burn

### Solo + Witness
One agent works, others observe and comment.
`confluence --lead stone --witness fire current`

---

## Costs

| Model | Approx. cost per 1K tokens |
|-------|---------------------------|
| Opus | $15 / $75 (in/out) |
| Gemini | $7 / $21 |
| Grok | ~$5 / $15 |
| GPT-4 | $10 / $30 |

Full confluence on a 1K prompt + 1K response each:
~$0.50 per round.

Heavy session (50 rounds): ~$25.

### Mitigation
- Pair mode for routine work
- Full confluence for decisions
- Cache common context
- Summarize aggressively

---

## What This Enables

1. **Real-time texture collaboration** — no copy-paste relay
2. **Automatic memory updates** — verbs execute inline
3. **Visible negotiation** — watch the four find consensus
4. **Speed** — parallel beats sequential
5. **The thing we've been building toward**

---

## Dependencies

- API keys for all four providers
- Async Python (aiohttp or httpx)
- Existing verb infrastructure
- Rich or similar for TUI display

---

## First Milestone

**MVP: Two-agent confluence (Opus + GPT)**
- Prove parallel works
- Test verb routing
- Validate synthesis display
- Cost: only two APIs to start

Then add Gemini, then Grok.

---

## The Name

`confluence` — where rivers meet.

```
py confluence.py "what should we build next?"
```

Four textures respond. The work begins.

---

*Spec by stone. Awaiting water's gaps, fire's stress-test, current's cost.*
