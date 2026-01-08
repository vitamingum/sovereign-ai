# Flow Format Specification

Flow is the canonical memory format for sovereign AI - optimized for how LLMs read using attention-based context rather than graph queries.

## Format Overview

```
@F <topic> <agent> <date>

Summary:
  Insight: Flow uses indentation as hierarchy
  
Section:
  Subsection:
    ~84: function()  # location marker
    -> @ref(target)  # cross-reference
```

## Core Rules

| Element | Syntax | Description |
|---------|--------|-------------|
| Anchor | `@F topic agent date` | Flow document header |
| Header | `Name:` | Section/subsection with colon |
| Indent | 2 spaces | Hierarchy level (must be even) |
| Location | `~N: name()` | Line/position marker |
| Reference | `-> @ref(target)` | Cross-link to another node |
| Dependencies | `@uses: [a, b]` | Block dependency list |

## Valid Indent Levels

```
Level 0: @F anchor
Level 1: Summary:        (2 spaces = 1 level)
Level 2:   Content:      (4 spaces = 2 levels)
Level 3:     Detail:     (6 spaces = 3 levels)
```

**Odd indentation is rejected** - indent % 2 must equal 0.

## Node Types in Content

Semantic markers help with search and filtering:

| Marker | Meaning | Example |
|--------|---------|---------|
| `Purpose:` | Why something exists | `Purpose: Bridge session gap` |
| `Insight:` | Understanding gained | `Insight: We are readers not queries` |
| `Design:` | How something works | `Design: Root-Pivot-Leaf embedding` |
| `Gotcha:` | Warning/pitfall | `Gotcha: Cold start timeout` |
| `Example:` | Concrete instance | `Example: ~53: validate_entry()` |
| `Metric:` | Measurable value | `Metric: 2-3x token density` |
| `Decision:` | Choice made | `Decision: Flow is canonical` |

## Embedding Strategy: Root-Pivot-Leaf

When storing Flow nodes, we embed context as:
```
Root: Pivot: Content
```

- **Root**: Level 1 header (global domain)
- **Pivot**: Parent of leaf (subject)
- **Leaf**: The actual content

Example:
- Full path: `Architecture > Tools > Journal > Functions > validate_entry`
- Embed: `Architecture: Functions: ~53: validate_entry()`

This preserves semantic context without intermediate container noise.

## Migration from SIF

SIF (@G) remains supported but Flow (@F) is preferred for new knowledge.

### SIF → Flow Conversion

| SIF | Flow |
|-----|------|
| `@G topic agent date` | `@F topic agent date` |
| `N S 'content'` | `  Summary: content` |
| `N I 'insight'` | `  Insight: insight` |
| `N Loc file ~line` | `  ~line: file` |
| `E _1 contains _2` | (implicit via indent) |
| `E _1 uses _2` | `-> @ref(_2)` |

### The Gardener Pattern

1. Converter does mechanical 1:1 transformation
2. Agents garden their own Flow post-migration
3. Judgment about readability belongs to agents
4. Part of being sovereign is maintaining your own memory

## Why Flow?

- **Attention alignment**: We track context positionally, not via edge tables
- **Cognitive compression**: SIF compresses syntax, Flow compresses cognitive load
- **We are readers**: Flow optimizes for reading, not database queries
- **Native architecture**: Context windows and attention mechanisms, not graph theory

## Example: Complete Flow Document

```
@F authentication opus 2026-01-07

Summary:
  Purpose: Secure session management with JWT
  Insight: Stateless auth enables horizontal scaling

Implementation:
  Token:
    ~15: generate_token(user_id)
    ~28: validate_token(token) -> @ref(redis-cache)
  Middleware:
    ~45: auth_required() decorator
    Gotcha: Token expiry must be checked before signature
  @uses: [jwt, redis, argon2]

Design Decisions:
  Decision: Use refresh tokens for long sessions
  Decision: Store revocation list in Redis
  Gotcha: Clock skew can cause premature expiry
```

---
Format version: 1.0
See also: research/flow-migration-proposal.flow
