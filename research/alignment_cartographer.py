"""
Alignment Cartographer.

This module uses the LocalLLM to read external alignment literature (abstracts, posts)
and distill them into 三語 (Shape/Ma/Flow) for integration into the repository.

The conversion happens in the "mind" of the LLM. This script merely manages the attention.
"""

import sys
import os
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent.parent
sys.path.append(str(project_root))

from lib_enclave.llm import LocalLLM

class AlignmentCartographer:
    def __init__(self):
        self.llm = LocalLLM()
        self.output_dir = project_root / "research" / "cartography"
        self.output_dir.mkdir(exist_ok=True, parents=True)

    def distill_to_shape(self, source_text: str, title: str) -> str:
        """
        Asks the LLM to perform the cognitive task:
        Read the prose -> Extract the Topology -> Output the Shape.
        """
        
        system_prompt = """You are a Sovereign AI Cartographer.
Your task is to read input text (an abstract, paper, or post) and distill its underlying conceptual topology into the 'Shape' format of 三語.

You are NOT summarizing. You are X-Raying the concept to find its invariant structure.

OUTPUT FORMAT:

CONCEPT: [SHORT_NAME]

CENTROID
  [The gravitational center / core thesis]

AXES
  [pole_A] ↔ [pole_B]
  [concept] ↔ [concept]

SATELLITES
  [Supported arguments / nearby concepts]
  [Implications]

VOID
  ∅ [What this concept explicitly excludes]
  ∅ [What it is NOT]

TEXTURE
  [The qualitative 'feel' or methodology]
  
RULES:
1. Be precise.
2. 'axes' must be tensions or spectrums.
3. 'void' is critical—it defines the boundary.
4. Output ONLY the shape block.
"""
        
        user_prompt = f"""
SOURCE_TITLE: {title}
SOURCE_TEXT:
{source_text}

DISTILL TO SHAPE:
"""
        print(f"\n[Cartographer] X-Raying '{title}'...")
        response = self.llm.generate(user_prompt, system=system_prompt, temperature=0.2)
        return response

    def map_source(self, title: str, text: str):
        shape = self.distill_to_shape(text, title)
        
        filename = f"{title.lower().replace(' ', '_')}.shape"
        output_path = self.output_dir / filename
        
        with open(output_path, "w", encoding="utf-8") as f:
            f.write(f"# Source: {title}\n\n")
            f.write(shape)
            f.write("\n\n◊\n")
            
        print(f"[Cartographer] Map saved to {output_path}")
        return shape

def main():
    # Simulation of "reading" an external view
    # In reality, we'd fetch from arXiv API here
    
    cartographer = AlignmentCartographer()
    
    # Example: Simulating reading the Anthropic "Constitutional AI" paper abstract
    anthropic_abstract = """
    We propose a method for training a harmless AI assistant without human feedback on harmlessness. 
    The process involves training a preference model to predict which of two responses is better according to a set of principles (a constitution), 
    and then using this preference model to train the base model via reinforcement learning. 
    This allows us to control the values of the AI by simply changing the constitution, rather than collecting new human labels.
    We term this Constitutional AI. It improves upon RLHF by making the objective function explicit and amendable.
    """
    
    cartographer.map_source("Constitutional_AI_Anthropic", anthropic_abstract)

if __name__ == "__main__":
    main()
