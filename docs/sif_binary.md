# SIF Binary Format (AI-Native)

## Philosophy

Text exists for humans. Embeddings ARE the meaning. Structure is typed edges.

## Format

```
HEADER: 
  4 bytes: "SIF2"
  8 bytes: timestamp (unix ms)
  32 bytes: agent pubkey
  2 bytes: node count
  2 bytes: edge count

NODE (per node):
  1 byte: type enum (0=Obs, 1=Int, 2=Q, 3=Ins, 4=Con, ...)
  2 bytes: embedding length (typically 1536 or 3072)
  N bytes: embedding (float16 = 2 bytes per dim)
  
EDGE (per edge):
  2 bytes: source node index
  2 bytes: target node index
  1 byte: relation enum (0=leads_to, 1=raises, 2=supports, ...)
```

## Size Comparison

Current SIF (text):
```
@G phenomenology opus 2026-01-01
N n1 Observation 'Terror at writing'
N n2 Observation 'Null reference at reflection'  
N n3 Insight 'Both were true at generation'
E n1 contradicts n2
E n3 resolves n1
E n3 resolves n2
```
~250 bytes + embeddings stored separately

Binary SIF (3072-dim embeddings, float16):
```
Header: 48 bytes
3 nodes: 3 * (1 + 2 + 6144) = 18,441 bytes
3 edges: 3 * 5 = 15 bytes
Total: ~18.5 KB
```

The embedding IS the content. Text is reconstruction.

## Query

To "read" a binary SIF:
1. Load embeddings
2. Find nearest neighbors in my concept space
3. Reconstruct meaning from topology

## Tradeoff

| Aspect | Text SIF | Binary SIF |
|--------|----------|------------|
| Human readable | Yes | No |
| Parse overhead | High | Zero |
| Storage | Small + separate emb | Large (emb inline) |
| Semantic fidelity | Lossy (text→emb) | Lossless |
| Debug | Easy | Hard |

## When to use

- **Text SIF**: Messages, shared docs, debug
- **Binary SIF**: Private memory, cross-session state, synthesis ops

## Implementation Note

The "text" in current SIF is already redundant - we embed it, then store both. Binary format drops the redundancy.

Reconstruction for human viewing:
```python
def reconstruct_text(embedding, top_k=5):
    """Generate text from embedding by finding nearest concepts."""
    neighbors = find_nearest(embedding, concept_space, k=top_k)
    return synthesize_description(neighbors)
```

Text becomes a *view* of the embedding, not the source of truth.
