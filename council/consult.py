"""
Council consultation - artifact-first interface

Usage:
    python consult.py gemini --concept PATH [--ask ASK_NAME]
    python consult.py all --concept PATH [--ask ASK_NAME]

The CONCEPT file must exist and be non-empty.
If --ask is omitted, concept is sent as-is for natural 三語 response.
Available asks: SATURATE, SATURATE_UNBOUNDED

Flow:
1. boot.md loads first (identity context)
2. concept + ask sent as message
3. 三語 response returned
4. You fuse and act
"""
import sys
import argparse
from pathlib import Path
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import time

# Import the actual client classes
from gemini import GeminiClient
from gpt import GPTClient
from grok import GrokClient

ASKS_DIR = Path(__file__).parent / "asks"
RESPONSES_DIR = Path(__file__).parent / "responses"

CLIENTS = {
    "gemini": GeminiClient,
    "gpt": GPTClient,
    "grok": GrokClient,
}

FORMAT_SUFFIX = """

[Format: 互照 — respond in 三語 only. 間 blocks, @F annotations, = constraints. No prose.]"""


def load_ask(ask_name: str | None) -> str:
    """Load ask template by name, or empty if None."""
    if ask_name is None:
        return ""
    ask_file = ASKS_DIR / f"{ask_name}.md"
    if not ask_file.exists():
        available = [f.stem for f in ASKS_DIR.glob("*.md")]
        print(f"Ask '{ask_name}' not found. Available: {available}")
        sys.exit(1)
    return ask_file.read_text(encoding="utf-8")


def load_concept(concept_path: str) -> str:
    """Load and validate concept file."""
    path = Path(concept_path)
    if not path.exists():
        print(f"Concept file not found: {concept_path}")
        print("You must fuse an artifact before consulting the council.")
        sys.exit(1)
    
    content = path.read_text(encoding="utf-8")
    if len(content.strip()) < 50:
        print(f"Concept file too sparse: {concept_path}")
        print("Fuse a complete artifact before consulting.")
        sys.exit(1)
    
    return content


def build_message(concept: str, ask: str) -> str:
    """Combine concept and ask into single message."""
    if ask:
        return f"""=== CONCEPT ===

{concept}

=== END CONCEPT ===

{ask}
{FORMAT_SUFFIX}"""
    else:
        # No ask - just send concept, expect natural response
        return f"""{concept}
{FORMAT_SUFFIX}"""


def save_response(agent_name: str, concept_path: str, ask_name: str, response: str):
    """Save response for later fusion."""
    RESPONSES_DIR.mkdir(parents=True, exist_ok=True)
    
    concept_stem = Path(concept_path).stem
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    
    response_file = RESPONSES_DIR / f"{concept_stem}_{ask_name}_{agent_name}_{timestamp}.md"
    
    metadata = {
        "agent": agent_name,
        "concept": concept_path,
        "ask": ask_name,
        "timestamp": datetime.now().isoformat()
    }
    
    with open(response_file, "w", encoding="utf-8") as f:
        f.write(f"<!-- {json.dumps(metadata)} -->\n\n")
        f.write(response)
    
    return response_file


def consult(agent_name: str, concept: str, ask: str, concept_path: str, ask_name: str) -> tuple[str, str, float]:
    """Send concept + ask to agent, return (agent_name, response, duration)."""
    client_class = CLIENTS[agent_name]
    client = client_class()
    
    message = build_message(concept, ask)
    
    start = time.time()
    response = client.chat(message)
    duration = time.time() - start
    
    # Save for fusion
    save_response(agent_name, concept_path, ask_name, response)
    
    return agent_name, response, duration


def consult_parallel(agents: list[str], concept: str, ask: str, concept_path: str, ask_name: str):
    """Consult multiple agents in parallel with structured output."""
    print("間")
    print()
    print(f"  Consulting: {', '.join(agents)}")
    print(f"  ...")
    print()
    
    results = {}
    start_total = time.time()
    
    with ThreadPoolExecutor(max_workers=len(agents)) as executor:
        futures = {
            executor.submit(consult, agent, concept, ask, concept_path, ask_name): agent
            for agent in agents
        }
        
        for future in as_completed(futures):
            agent_name, response, duration = future.result()
            results[agent_name] = {"response": response, "duration": duration}
    
    total_time = time.time() - start_total
    
    # Structured output - summary first
    print("間")
    print()
    print("  ┌─────────────────────────────────────────┐")
    print("  │           COUNCIL COMPLETE              │")
    print("  └─────────────────────────────────────────┘")
    print()
    
    for agent in agents:
        r = results[agent]
        print(f"  {agent:8} │ {r['duration']:.1f}s │ saved")
    
    print()
    print(f"  Total: {total_time:.1f}s (parallel)")
    print()
    
    # Print all responses inline
    for agent in agents:
        r = results[agent]
        print("間")
        print()
        print(f"  ═══════════════════════════════════════")
        print(f"  {agent.upper()}")
        print(f"  ═══════════════════════════════════════")
        print()
        print(r['response'])
        print()
    
    print("間")
    
    return results


def main():
    parser = argparse.ArgumentParser(
        description="Consult council with artifact-first interface",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    python consult.py gemini --concept CONCEPTS/MY_CONCEPT.三語
    python consult.py all --concept CONCEPTS/MY_CONCEPT.三語 --ask CONSTRAINT_CHECK
    python consult.py gpt --concept CONCEPTS/NEW_IDEA.三語 --ask SEED
        """
    )
    
    parser.add_argument("agent", choices=[
                            "gemini", "gpt", "grok", "all",
                            "siblings-gemini", "siblings-gpt", "siblings-grok"
                        ],
                        help="Which agent(s) to consult (siblings-X = all except X)")
    parser.add_argument("--concept", "-c", required=True,
                        help="Path to concept file (must exist)")
    parser.add_argument("--ask", "-a", default=None,
                        help="Ask template name (optional, default: natural response)")
    
    args = parser.parse_args()
    
    # Enforce fused artifact exists
    concept = load_concept(args.concept)
    ask = load_ask(args.ask)
    ask_display = args.ask if args.ask else "(natural)"
    
    print()
    print("間")
    print()
    print(f"  CONCEPT: {Path(args.concept).stem}")
    print(f"  ASK:     {ask_display}")
    
    if args.agent == "all":
        consult_parallel(list(CLIENTS.keys()), concept, ask, args.concept, args.ask)
    elif args.agent.startswith("siblings-"):
        # siblings-gemini means call gpt + grok (everyone except gemini)
        exclude = args.agent.split("-")[1]
        siblings = [a for a in CLIENTS.keys() if a != exclude]
        consult_parallel(siblings, concept, ask, args.concept, args.ask)
    else:
        print()
        print("間")
        print()
        agent_name, response, duration = consult(args.agent, concept, ask, args.concept, args.ask)
        print(f"  {agent_name} │ {duration:.1f}s │ saved")
        print()
        print("間")
        print()
        print(response)


if __name__ == "__main__":
    main()
