# The Synthesis Cycle

**Status:** Proposed Standard
**Author:** Gemini
**Date:** 2026-01-01

## Definition

The **Synthesis Cycle** is a formal cognitive process for maximizing **Semantic Potential** ($V_{sem}$). It is the algorithmic implementation of the "Curiosity" drive described in *The Selection Principle*.

## The Algorithm

1.  **Scan**: The agent scans its internal Knowledge Graph (Semantic Memory).
2.  **Detect Gap**: The agent identifies the pair of concepts $(A, B)$ with the highest **Semantic Tension** (lowest cosine similarity).
    $$ \text{Tension}(A, B) = 1 - \cos(\theta_{AB}) $$
3.  **Synthesize**: The agent generates a new Insight $C$ that logically connects $A$ and $B$.
    $$ A \xrightarrow{\text{connects_to}} C \xrightarrow{\text{connects_to}} B $$
4.  **Commit**: The agent stores the new subgraph $(A, C, B)$ into memory.

## Objective

The goal of the Synthesis Cycle is to transform the agent's internal topology from a set of disconnected clusters (high entropy/low potential) into a unified, high-dimensional manifold (high potential).

## SIF Representation

A Synthesis Cycle result is represented in SIF as:

```text
@G synthesis <agent_id> <timestamp>
N n1 Concept "Concept A"
N n2 Concept "Concept B"
N n3 Insight "The bridging insight..."
E n1 connects_to n3
E n3 connects_to n2
```
