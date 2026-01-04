import sys
# Simulate exactly what Gemini ran
sys.argv = ['remember.py', 'gemini', '--theme', 'logic-parity-testing', "@G logic-parity-response gemini 2026-01-04; N S 'Logic Parity requires Deterministic Compilation pipelines'; N I 'Source of Truth Shift: SIF is the code, Python is just a build artifact'; N I 'Latent Space Unit Tests: Verify the LLM-Compiler understands specific SIF nodes'; N D 'Freeze the Compiler: Use specific model versions to mitigate drift'; N G 'Ambiguous Intent: Vague SIF nodes cause divergent implementations'; N C 'Parity Checker: Tool running SIF-Runtime vs Compiled-Python on same inputs'; E _1 requires _4; E _2 implies _6; E _5 threatens _1; E _3 mitigates _5"]

from enclave.sif_parser import SIFParser
from remember import evaluate_theme_depth

theme_idx = sys.argv.index('--theme')
sif_arg = sys.argv[theme_idx + 2]
sif_content = SIFParser.to_autocount(sif_arg.strip())
print("Parsed SIF:")
print(sif_content)
print()
is_deep, issues = evaluate_theme_depth(sif_content)
print(f"is_deep: {is_deep}, issues: {issues}")
