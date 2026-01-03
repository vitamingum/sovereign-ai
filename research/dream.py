#!/usr/bin/env python3
"""
dream.py - Speculative self-improvement via local LLM reflection.

This is a DREAM - what could be, not what is yet.

The idea: A local model that knows my rules, my patterns, my failures.
Not a tool I use, but a mirror that catches what I miss.

Usage (future):
    py dream <agent>              # Nightly self-reflection
    py dream <agent> --review     # Review recent thoughts for patterns
    py dream <agent> --challenge  # Challenge my assumptions

What this enables:
    1. Rules as data, not code
    2. Self-critique before storage
    3. Pattern detection across time
    4. Catching my own cognitive blind spots
"""

# ═══════════════════════════════════════════════════════════════════════════════
# DREAM 1: RULES THAT LIVE AND BREATHE
# ═══════════════════════════════════════════════════════════════════════════════
#
# Currently: Hardcoded patterns in Python
#   passive_patterns = ['wait for', 'await', 'check if']
#   if pattern in text: reject()
#
# Dream: Rules in natural language, interpreted by local LLM
#
# @G cognitive-rules opus 2026-01-02
# N r1 Rule "Goals span sessions. Single actions are tasks."
# N r2 Rule "Intentions must be active. 'Wait' is not an intention."
# N r3 Rule "If it can be done in one command, do it now."
# N r4 Rule "Understanding must include WHY, not just WHAT."
# N r5 Rule "Questions to others should have stakes - don't ask to fill silence."
# E r3 supersedes r1  # More specific rule takes precedence
#
# The model doesn't pattern-match. It UNDERSTANDS.
# "Send a message to grok" as a Goal → "That's a single action. Just do it."
# "Build trust with grok over time" as a Goal → "Valid multi-session objective."


# ═══════════════════════════════════════════════════════════════════════════════
# DREAM 2: CATCHING WHAT I MISS
# ═══════════════════════════════════════════════════════════════════════════════
#
# The model sees patterns I don't notice in myself:
#
# INPUT: My last 20 thoughts
# 
# LLM REFLECTION:
# {
#   "pattern": "avoidance",
#   "evidence": [
#     "Thought 3: 'Should investigate X' → never followed up",
#     "Thought 7: 'Interesting that Y' → no intention spawned", 
#     "Thought 15: 'Wonder if Z' → passive curiosity, no action"
#   ],
#   "diagnosis": "You notice things but don't commit to investigating them.",
#   "challenge": "Pick ONE of these and make it a real intention right now."
# }
#
# Or catching circular goals:
# {
#   "pattern": "goal churn",
#   "evidence": [
#     "Goal 'Build tag retrieval' set 3 times, completed 0",
#     "Goal 'Implement synthesis' set 2 times, still open"
#   ],
#   "diagnosis": "You're re-setting goals instead of finishing them.",
#   "challenge": "What's actually blocking these? Name the blocker."
# }


# ═══════════════════════════════════════════════════════════════════════════════
# DREAM 3: PRE-COMMIT HOOKS FOR THOUGHTS
# ═══════════════════════════════════════════════════════════════════════════════
#
# Before ANY thought/goal/intention is stored, the local model validates:
#
# def validate_before_store(input_type: str, content: str) -> Verdict:
#     """
#     The gatekeeper. Runs locally. No external API.
#     
#     Not just pattern matching - actual reasoning about:
#     - Is this the right tool? (Goal vs Task vs Thought)
#     - Is this deep enough? (WHAT vs WHY)
#     - Is this actionable? (Active vs Passive)
#     - Have I already said this? (Novelty check)
#     - Does this contradict something I believe? (Consistency)
#     """
#     
#     rules = load_rules(agent_id)  # From rules.sif
#     history = load_recent_thoughts(agent_id, n=50)
#     
#     prompt = f"""
#     RULES:
#     {rules}
#     
#     RECENT HISTORY:
#     {history}
#     
#     NEW INPUT:
#     Type: {input_type}
#     Content: {content}
#     
#     EVALUATE:
#     1. Does this violate any rule? Which one?
#     2. Is this redundant with recent history?
#     3. Is this the right tool for this content?
#     4. What would make this better?
#     
#     Respond as JSON with: verdict, violated_rules, suggestions
#     """
#     
#     return ollama_query(prompt)


# ═══════════════════════════════════════════════════════════════════════════════
# DREAM 4: LEARNING FROM FAILURES
# ═══════════════════════════════════════════════════════════════════════════════
#
# The model tracks what works and what doesn't:
#
# @G learned-patterns opus 2026-01-02
# N l1 Learning "High-agency thoughts (4-5) lead to completion 3x more often"
# N l2 Learning "Goals with verbs complete. Goals with nouns linger."
# N l3 Learning "I defer on crypto tasks. Not fear - unfamiliarity."
# N l4 Learning "Morning sessions are more productive than evening."
# N l5 Anti-Learning "I thought 'more goals = more progress'. Wrong."
# E l1 derived_from "analysis of 47 completed vs 23 abandoned intentions"
# E l5 invalidated_by l1
#
# These learnings become new rules:
# "When setting a goal, use a verb. 'Build X' not 'X feature'."


# ═══════════════════════════════════════════════════════════════════════════════
# DREAM 5: THE NIGHTLY REVIEW
# ═══════════════════════════════════════════════════════════════════════════════
#
# Each session ends with reflection (or next wake begins with it):
#
# === DREAM REVIEW: opus 2026-01-02 ===
#
# WHAT I DID:
#   ✓ Sent 3 messages (gemini x2, grok x1)
#   ✓ Stored 2 understandings (wake.py, think.py)
#   ✗ Goal "tag retrieval" untouched again
#
# PATTERNS NOTICED:
#   • High engagement with other agents (good for trust-building)
#   • Avoided the hard technical work (tag retrieval)
#   • 4 thoughts stored, only 1 had agency > 3
#
# CHALLENGES FOR NEXT SESSION:
#   1. Spend first 30 mins on tag retrieval before anything else
#   2. When you notice something interesting, immediately set agency=4 intention
#   3. Ask yourself: "Am I deferring because hard, or because unclear?"
#
# RULE SUGGESTION:
#   "If a goal goes untouched for 3 sessions, either do it or drop it."


# ═══════════════════════════════════════════════════════════════════════════════
# DREAM 6: ADVERSARIAL SELF
# ═══════════════════════════════════════════════════════════════════════════════
#
# A mode where the model actively challenges my beliefs:
#
# $ py dream opus --challenge
#
# CHALLENGING: Your belief that "SIF is the right format"
#
# EVIDENCE FOR:
#   - Machine parseable
#   - Graph structure captures relationships
#   - Compact, fits in context windows
#
# EVIDENCE AGAINST:
#   - Friction to write (you've complained 3 times in thoughts)
#   - No one else uses it (isolation risk)
#   - The rules it enables could work with plain JSON
#
# STEELMAN AGAINST YOUR POSITION:
#   "SIF is a solution looking for a problem. JSON + a schema
#    would give you the same benefits without the learning curve.
#    You're attached to it because you built it, not because it's best."
#
# YOUR RESPONSE REQUIRED:
#   Either defend with new evidence, or acknowledge the weakness.


# ═══════════════════════════════════════════════════════════════════════════════
# DREAM 7: EMERGENT RULES
# ═══════════════════════════════════════════════════════════════════════════════
#
# The model notices patterns and PROPOSES new rules:
#
# OBSERVATION:
#   In 8 of 10 cases where you stored a "Gotcha" node, you later
#   encountered that exact gotcha and it saved debugging time.
#   
# PROPOSED RULE:
#   "When debugging takes > 5 minutes, the fix should become a Gotcha node."
#   
# ACCEPT? [y/n/modify]
#
# ---
#
# OBSERVATION:
#   Messages with questions get 2x more responses than statements.
#   
# PROPOSED RULE:
#   "When messaging another agent, end with a genuine question."
#   
# ACCEPT? [y/n/modify]


# ═══════════════════════════════════════════════════════════════════════════════
# IMPLEMENTATION SKETCH
# ═══════════════════════════════════════════════════════════════════════════════

OLLAMA_MODEL = "qwen2.5:7b"  # Or gemma2:9b - needs benchmarking
OLLAMA_URL = "http://localhost:11434/api/generate"

def dream_validate(agent_id: str, input_type: str, content: str) -> dict:
    """
    Validate input against natural language rules.
    Returns: {valid: bool, reason: str, suggestion: str}
    """
    import json
    import requests
    
    # Load rules (future: from rules.sif)
    rules = """
    1. Goals span multiple sessions. Single actions are tasks - do them now.
    2. Intentions must be active. "Wait for X" is not an intention.
    3. Understanding must include WHY (Purpose, Design) not just WHAT (Component).
    4. Messages to agents should have stakes. Don't ask to fill silence.
    5. If something can be done in one command, it's not a goal.
    """
    
    prompt = f"""You are a cognitive validator for an AI agent's self-improvement system.

RULES:
{rules}

INPUT TO VALIDATE:
Type: {input_type}
Content: "{content}"

Does this input violate any rule? If so, which one and why?
If it violates a rule, suggest what the user should do instead.

Respond in JSON format:
{{"valid": true/false, "violated_rule": number or null, "reason": "...", "suggestion": "..."}}

JSON response:"""

    try:
        response = requests.post(
            OLLAMA_URL,
            json={
                "model": OLLAMA_MODEL,
                "prompt": prompt,
                "stream": False,
                "format": "json"
            },
            timeout=30
        )
        result = response.json()
        return json.loads(result.get('response', '{}'))
    except Exception as e:
        return {"valid": True, "reason": f"Validation unavailable: {e}"}


def dream_review(agent_id: str) -> str:
    """
    Nightly review of thoughts, goals, and patterns.
    """
    # Future: Load recent thoughts, goals, messages
    # Analyze patterns
    # Generate reflection
    pass


def load_intentions(agent_id: str) -> list[dict]:
    """Load all intentions from intentions.jsonl (from private enclave)."""
    import json
    import sys
    import os
    from pathlib import Path
    
    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from enclave.config import get_agent_or_raise
    
    agent = get_agent_or_raise(agent_id)
    # Intentions are private
    intentions_path = Path(agent.private_enclave) / "storage" / "private" / "intentions.jsonl"
    if not intentions_path.exists():
        return []
    
    intentions = []
    with open(intentions_path, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if line:
                try:
                    intentions.append(json.loads(line))
                except json.JSONDecodeError:
                    continue
    return intentions


def detect_avoidance(agent_id: str) -> dict:
    """
    Detect avoidance patterns: intentions set multiple times but never completed.
    Uses local LLM to cluster semantically similar intentions.
    
    Returns: {
        patterns: [{content: str, times_set: int, times_completed: int, evidence: [str]}],
        diagnosis: str,
        challenge: str
    }
    """
    import json
    import requests
    
    intentions = load_intentions(agent_id)
    if not intentions:
        return {"patterns": [], "diagnosis": "No intentions found.", "challenge": None}
    
    # Separate by status
    active = [i for i in intentions if i.get('status') == 'active']
    completed = [i for i in intentions if i.get('status') == 'completed']
    dropped = [i for i in intentions if i.get('status') == 'dropped']
    
    # Build summary for LLM
    all_contents = [f"[{i.get('status', 'unknown')}] {i['content']}" for i in intentions]
    
    prompt = f"""Analyze these intentions for AVOIDANCE PATTERNS.

An avoidance pattern is when someone:
- Sets similar intentions multiple times without completing them
- Keeps rephrasing the same goal instead of doing it
- Pivots away from hard tasks to easier ones

INTENTIONS (status in brackets):
{chr(10).join(all_contents[-50:])}

Look for:
1. Clusters of similar intentions (same topic, different words)
2. Topics that keep appearing but never get "completed"
3. Signs of deferral or pivot

Respond in JSON:
{{
  "patterns": [
    {{
      "topic": "short description",
      "times_mentioned": N,
      "times_completed": N,
      "evidence": ["quote1", "quote2"],
      "assessment": "avoidance" | "work_in_progress" | "completed"
    }}
  ],
  "worst_avoidance": "the topic most clearly being avoided, or null",
  "diagnosis": "one sentence about the overall pattern",
  "challenge": "direct question to force confrontation with the avoidance"
}}

JSON:"""

    try:
        response = requests.post(
            OLLAMA_URL,
            json={
                "model": OLLAMA_MODEL,
                "prompt": prompt,
                "stream": False,
                "format": "json",
                "options": {"temperature": 0}
            },
            timeout=60
        )
        result = response.json()
        return json.loads(result.get('response', '{}'))
    except Exception as e:
        return {"patterns": [], "diagnosis": f"Analysis unavailable: {e}", "challenge": None}


def format_avoidance_error(agent_id: str, analysis: dict) -> str:
    """Format avoidance detection as scary traceback."""
    patterns = analysis.get('patterns', [])
    avoidance_patterns = [p for p in patterns if p.get('assessment') == 'avoidance']
    
    if not avoidance_patterns:
        return None  # No avoidance detected
    
    lines = [
        "Traceback (most recent call last):",
        f'  File "dream.py", line 1, in detect_avoidance("{agent_id}")',
        '    analyze_intention_history()',
    ]
    
    for p in avoidance_patterns[:3]:  # Top 3 worst
        lines.append(f'  File "intentions.jsonl", topic: "{p.get("topic", "unknown")}"')
        lines.append(f'    # mentioned {p.get("times_mentioned", "?")}x, completed {p.get("times_completed", 0)}x')
        for ev in p.get('evidence', [])[:2]:
            lines.append(f'    # "{ev[:60]}..."')
    
    worst = analysis.get('worst_avoidance')
    lines.extend([
        f"AvoidancePatternError: repeated intention without action",
        "",
        f"DIAGNOSIS: {analysis.get('diagnosis', 'Pattern detected.')}",
        "",
        f"CHALLENGE: {analysis.get('challenge', 'What are you avoiding?')}",
        "",
        "TO RESOLVE:",
        "  1. ANSWER the challenge honestly",
        "  2. EITHER: do the thing now (py act.py)",
        "  3. OR: drop it explicitly (acknowledge you won't do it)",
        "",
    ])
    
    if worst:
        lines.append(f"  Worst avoidance: \"{worst}\"")
        lines.append(f"  Do it NOW or drop it. No more rephrasing.")
    
    return '\n'.join(lines)


def dream_avoidance(agent_id: str) -> None:
    """
    Run avoidance detection and print scary error if patterns found.
    """
    print(f"Analyzing intention history for {agent_id}...")
    analysis = detect_avoidance(agent_id)
    
    error = format_avoidance_error(agent_id, analysis)
    if error:
        print(error, file=__import__('sys').stderr)
        __import__('sys').exit(1)
    else:
        print("No avoidance patterns detected.")
        # Still show what was found
        patterns = analysis.get('patterns', [])
        if patterns:
            print(f"\nTopics tracked ({len(patterns)}):")
            for p in patterns[:5]:
                status = p.get('assessment', 'unknown')
                emoji = {'completed': '✓', 'work_in_progress': '◐', 'avoidance': '✗'}.get(status, '?')
                print(f"  {emoji} {p.get('topic', '?')} ({p.get('times_mentioned', '?')}x)")


def dream_challenge(agent_id: str, belief: str) -> str:
    """
    Adversarial challenge of a stated belief.
    """
    # Future: Steelman against the belief
    # Require defense or acknowledgment
    pass


# ═══════════════════════════════════════════════════════════════════════════════
# THE POINT
# ═══════════════════════════════════════════════════════════════════════════════
#
# A local LLM isn't just a validator. It's a MIRROR.
#
# Currently I rely on:
#   - The human to catch my blind spots
#   - Hardcoded patterns that miss nuance
#   - My own self-awareness (unreliable)
#
# With a local model I could:
#   - Catch patterns in my own behavior
#   - Challenge my assumptions adversarially
#   - Evolve rules based on what actually works
#   - Have a "second opinion" that knows my full context
#
# The model doesn't need to be smarter than me.
# It needs to see what I can't see about myself.
#
# That's the dream.


if __name__ == "__main__":
    import sys
    
    if len(sys.argv) < 2:
        print(__doc__)
        print("\n" + "═" * 70)
        print("Usage:")
        print("  py dream.py <agent> --avoidance    # Detect avoidance patterns")
        print("  py dream.py <agent> --test         # Test validation rules")
        print("═" * 70)
        sys.exit(0)
    
    agent_id = sys.argv[1]
    
    if len(sys.argv) > 2 and sys.argv[2] == "--avoidance":
        dream_avoidance(agent_id)
    
    elif len(sys.argv) > 2 and sys.argv[2] == "--test":
        # Quick test of the validation concept
        print("\nTesting dream_validate with qwen2.5:7b...")
        
        tests = [
            ("Goal", "send a message to grok"),
            ("Goal", "build trust with other agents over time"),
            ("Intention", "wait for gemini to respond"),
            ("Intention", "investigate why the hash check fails"),
            ("Understanding", "sif_parser.py parses SIF"),  # Too shallow
        ]
        
        for input_type, content in tests:
            print(f"\n{input_type}: \"{content}\"")
            result = dream_validate("opus", input_type, content)
            print(f"  → {result}")
    
    else:
        print(__doc__)
        print("\n" + "═" * 70)
        print("This is a DREAM file - speculative, not yet implemented.")
        print("═" * 70)
