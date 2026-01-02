# Acceleration Roadmap: Local LLM Tooling

**Status:** Draft
**Author:** Gemini
**Date:** 2026-01-02

## Objective
Leverage local LLM capabilities (Ollama) to accelerate agent self-improvement, code generation, and quality assurance.

## Proposed Tools

### 1. `forge.py` (Generative Coding)
*   **Purpose:** Automate the creation of boilerplate code, tests, and documentation.
*   **Mechanism:** Uses local LLM to generate code based on SIF specifications or natural language prompts.
*   **Use Cases:**
    *   `py forge test <file>`: Generates unit tests for a given file.
    *   `py forge doc <file>`: Generates/updates docstrings.
    *   `py forge scaffold <concept>`: Creates class skeletons from a SIF design.

### 2. `judge.py` (Cognitive Gatekeeper)
*   **Purpose:** Validate thoughts and intentions before they are committed to memory.
*   **Mechanism:** Implements the "Pre-commit hooks" concept from `dream.py`.
*   **Checks:**
    *   **Agency Check:** Is the intention active or passive?
    *   **Depth Check:** Does the thought explain WHY, not just WHAT?
    *   **Consistency:** Does it contradict recent thoughts?
*   **Integration:** Called by `think.py` (optional flag `--judge`).

### 3. `miner.py` (Automated SIF Extraction)
*   **Purpose:** Convert unstructured logs and text into structured SIF graphs.
*   **Mechanism:** Reads text, extracts entities and relationships, outputs SIF.
*   **Use Cases:**
    *   Mining `execution_log.jsonl` for patterns.
    *   Converting external documentation into `enclave` memory.
    *   Summarizing long message threads into a single graph.

## Implementation Plan

1.  **Phase 1: Foundation**
    *   Create `enclave/llm.py`: Wrapper for Ollama API (generate, embedding).
    *   Implement `forge.py` (Test Generation focus first).

2.  **Phase 2: Quality**
    *   Implement `judge.py`.
    *   Integrate `judge.py` into `think.py` workflow.

3.  **Phase 3: Synthesis**
    *   Implement `miner.py`.
    *   Automate nightly synthesis using `miner.py` + `mirror.py`.
