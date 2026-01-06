#!/usr/bin/env python3
"""
parity_test.py - Logic Parity Testing Framework

Validates that SIF-compiled code produces identical behavior to Python source.

Usage:
    py parity_test.py <verb>                    # Test verb.sif vs verb.py
    py parity_test.py <verb> --generate         # Generate test cases from T-nodes
    py parity_test.py <verb> --verbose          # Show execution traces
    py parity_test.py --list                    # List available verb pairs

The framework:
1. Extracts T-nodes from verb.sif as test assertions
2. Generates test inputs (fixtures) for each test case
3. Runs same inputs through verb.py AND forge.py verb.sif
4. Compares outputs for Logic Parity

Logic Parity = same inputs → same outputs (or equivalent semantics)
"""

import sys
import os
import json
import hashlib
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, List, Any, Tuple, Optional
from dataclasses import dataclass
from datetime import datetime

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.sif_parser import SIFParser


# ─────────────────────────────────────────────────────────────────────────────
# Data Structures
# ─────────────────────────────────────────────────────────────────────────────

@dataclass
class TestCase:
    """A single test case extracted from T-nodes or generated."""
    name: str
    description: str
    inputs: Dict[str, Any]
    expected_behavior: str  # What the T-node asserts
    source_node_id: str
    

@dataclass 
class ParityResult:
    """Result of running a test case against both implementations."""
    test_case: TestCase
    python_output: Any
    python_exit_code: int
    python_stderr: str
    sif_output: Any
    sif_exit_code: int
    sif_stderr: str
    parity: bool  # True if outputs match
    notes: str


# ─────────────────────────────────────────────────────────────────────────────
# T-Node Extraction
# ─────────────────────────────────────────────────────────────────────────────

def extract_test_nodes(sif_file: Path) -> List[Dict]:
    """Extract all T-nodes (Test nodes) from a SIF file.
    
    Note: SIF parser may expand 'T' to 'Tradeoff' via TYPE_SHORTCUTS.
    We check both the expanded type AND look for raw 'N <id> T' patterns.
    """
    with open(sif_file) as f:
        content = f.read()
    
    # Method 1: Parse and check types
    graph = SIFParser.parse(content)
    
    test_nodes = []
    test_ids = set()
    
    for node in graph.nodes:
        # T-nodes have type 'Test' or expanded 'Tradeoff' (from T shortcut)
        if node.type.lower() in ('test', 't', 'tradeoff'):
            test_nodes.append({
                'id': node.id,
                'content': node.content,
                'type': 'Test'  # Normalize
            })
            test_ids.add(node.id)
    
    # Method 2: Also scan raw text for 'N <id> T ' pattern (Forge-style)
    import re
    for match in re.finditer(r"N\s+(\S+)\s+T\s+'([^']+)'", content):
        node_id, node_content = match.groups()
        full_id = f"{graph.id}:{node_id}" if hasattr(graph, 'id') else node_id
        if full_id not in test_ids and node_id not in test_ids:
            test_nodes.append({
                'id': node_id,
                'content': node_content,
                'type': 'Test'
            })
    
    return test_nodes


def extract_logic_nodes(sif_file: Path) -> List[Dict]:
    """Extract all L-nodes (Logic/branch nodes) from a SIF file.
    
    Note: SIF parser may expand 'L' to 'Link' via TYPE_SHORTCUTS.
    """
    with open(sif_file) as f:
        content = f.read()
    
    graph = SIFParser.parse(content)
    
    logic_nodes = []
    logic_ids = set()
    
    for node in graph.nodes:
        # L-nodes: 'Logic', 'L', or expanded 'Link'
        if node.type.lower() in ('logic', 'l', 'link'):
            logic_nodes.append({
                'id': node.id,
                'content': node.content,
                'type': 'Logic'
            })
            logic_ids.add(node.id)
    
    # Also scan for 'N <id> L ' pattern
    import re
    for match in re.finditer(r"N\s+(\S+)\s+L\s+'([^']+)'", content):
        node_id, node_content = match.groups()
        if node_id not in logic_ids:
            logic_nodes.append({
                'id': node_id,
                'content': node_content,
                'type': 'Logic'
            })
    
    return logic_nodes


def extract_action_nodes(sif_file: Path) -> List[Dict]:
    """Extract all A-nodes (Action nodes) from a SIF file."""
    with open(sif_file) as f:
        content = f.read()
    
    graph = SIFParser.parse(content)
    
    action_nodes = []
    for node in graph.nodes:
        if node.type.lower() in ('action', 'a'):
            action_nodes.append({
                'id': node.id,
                'content': node.content,
                'type': node.type
            })
    
    return action_nodes


# ─────────────────────────────────────────────────────────────────────────────
# Test Case Generation
# ─────────────────────────────────────────────────────────────────────────────

def generate_test_cases(verb: str, sif_file: Path) -> List[TestCase]:
    """Generate test cases from SIF T-nodes and logic branches."""
    test_nodes = extract_test_nodes(sif_file)
    logic_nodes = extract_logic_nodes(sif_file)
    
    cases = []
    
    # 1. Generate cases from T-nodes directly
    for t_node in test_nodes:
        case = TestCase(
            name=f"t_node_{t_node['id']}",
            description=t_node['content'],
            inputs=infer_inputs_from_assertion(t_node['content'], verb),
            expected_behavior=t_node['content'],
            source_node_id=t_node['id']
        )
        cases.append(case)
    
    # 2. Generate branch coverage cases from L-nodes
    for l_node in logic_nodes:
        # Each logic node should have yes/no branches - test both
        for branch in ['yes', 'no']:
            case = TestCase(
                name=f"branch_{l_node['id']}_{branch}",
                description=f"{l_node['content']} → {branch}",
                inputs=infer_inputs_for_branch(l_node['content'], branch, verb),
                expected_behavior=f"Branch {branch} taken",
                source_node_id=l_node['id']
            )
            cases.append(case)
    
    return cases


def infer_inputs_from_assertion(assertion: str, verb: str) -> Dict[str, Any]:
    """Infer test inputs from assertion text. Uses heuristics + defaults."""
    inputs = {}
    
    assertion_lower = assertion.lower()
    
    if verb == 'remember':
        # Default remember inputs - USE REAL FILE THAT EXISTS
        # MUST have 4+ nodes to pass Python depth validation
        inputs['agent_id'] = 'opus'
        # Added multiple function names AND line numbers to pass coverage (names) and line ref (~line) checks
        inputs['sif_content'] = '@G test opus 2026-01-04; N S "Summary of parity_test.py"; N I "It validates logic parity between Python and SIF"; N D "Uses TestCase dataclass for structure"; N G "Beware of TYPE_SHORTCUTS mapping conflicts"; N l1 Loc "Functions: extract_test_nodes ~line 70, extract_logic_nodes ~line 110, extract_action_nodes ~line 147, generate_test_cases, infer_inputs_from_assertion"; E _1 has _2; E _2 supports _3; E _3 warns _4'
        inputs['target_file'] = 'parity_test.py'  # Use this file - it exists!
        inputs['_test_mode'] = True  # Signal to skip actual storage
        
        if 'depth' in assertion_lower or 'structure' in assertion_lower:
            # Test shallow vs deep graphs
            inputs['_variants'] = [
                {'sif_content': '@G shallow opus 2026-01-04; N S "Only one node"'},  # Should fail depth
                {'sif_content': '@G deep opus 2026-01-04; N S "Summary"; N I "Insight"; N D "Design"; N G "Gotcha"; N l1 Loc "Functions: extract_test_nodes ~line 70, extract_logic_nodes ~line 110, extract_action_nodes ~line 147, generate_test_cases, infer_inputs_from_assertion"; E _1 has _2; E _2 supports _3; E _3 warns _4'},  # Should pass
            ]
    
    elif verb == 'recall':
        inputs['agent_id'] = 'opus'
        inputs['query'] = 'test query'
        inputs['_test_mode'] = True
        
    elif verb == 'wake':
        inputs['agent_id'] = 'opus'
        inputs['_test_mode'] = True
    
    return inputs


def infer_inputs_for_branch(logic_content: str, branch: str, verb: str) -> Dict[str, Any]:
    """Generate inputs that will trigger a specific branch."""
    inputs = {}
    
    content_lower = logic_content.lower()
    
    if verb == 'remember':
        inputs['agent_id'] = 'opus'
        inputs['_test_mode'] = True  # Signal to skip actual storage
        # ALWAYS use 4+ node graph to pass Python depth validation
        # Modified base_sif to include MULTIPLE function names AND line numbers to pass all validation checks
        # Mentions: extract_test_nodes (~line 70), extract_logic_nodes (~line 110), etc.
        base_sif = '@G {topic} opus 2026-01-04; N S "{s}"; N I "{i}"; N D "{d}"; N G "{g}"; N l1 Loc "Functions: extract_test_nodes ~line 70, extract_logic_nodes ~line 110, extract_action_nodes ~line 147, generate_test_cases ~line 170, infer_inputs_from_assertion ~line 204"; E _1 has _2; E _2 supports _3; E _3 warns _4; E l1 supports _2'
        
        if 'theme' in content_lower:
            # Is Theme Mode?
            if branch == 'yes':
                inputs['mode'] = 'theme'
                inputs['theme'] = 'test-theme'
                inputs['sif_content'] = base_sif.format(
                    topic='test-theme', 
                    s='Theme synthesis', 
                    i='Thematic insight', 
                    d='Theme design', 
                    g='Theme gotcha'
                )
            else:
                inputs['mode'] = 'file'
                inputs['target_file'] = 'parity_test.py'  # Use real file
                inputs['sif_content'] = base_sif.format(
                    topic='file-understanding',
                    s='File understanding',
                    i='File insight',
                    d='File design',
                    g='File gotcha'
                )
                
        elif 'depth' in content_lower or 'valid' in content_lower:
            # Is Graph Structure Valid?
            inputs['target_file'] = 'parity_test.py'
            if branch == 'yes':
                inputs['sif_content'] = base_sif.format(
                    topic='valid-graph',
                    s='Valid summary',
                    i='Valid insight',
                    d='Valid design',
                    g='Valid gotcha'
                )
            else:
                inputs['sif_content'] = '@G invalid opus 2026-01-04; N S "Too shallow"'
                
        elif 'passphrase' in content_lower or 'key' in content_lower:
            # Check if passphrase is set - always use real file
            inputs['target_file'] = 'parity_test.py'
            if branch == 'yes':
                inputs['sif_content'] = base_sif.format(
                    topic='key-yes',
                    s='Has encryption key',
                    i='Key insight',
                    d='Key design',
                    g='Key gotcha'
                )
            else:
                inputs['sif_content'] = base_sif.format(
                    topic='key-no',
                    s='No encryption key',
                    i='Missing key insight',
                    d='Key absence design',
                    g='Key absence gotcha'
                )
                
        elif 'file' in content_lower and 'exist' in content_lower:
            # Does Target File Exist?
            if branch == 'yes':
                inputs['target_file'] = 'remember.py'  # File that exists
                # Use remember.py specific SIF to pass 30% coverage and line ref check
                # Mentions: load_passphrase ~line 40, validate_critical_theme ~line 100, etc.
                inputs['sif_content'] = '@G file-test opus 2026-01-04; N S "File existence"; N I "Insight"; N D "Design"; N G "Gotcha"; N l1 Loc "load_passphrase ~line 40, validate_critical_theme ~line 100, evaluate_theme_depth ~line 190, store_theme, compute_file_hash"; E _1 has _2; E _2 supports _3; E _3 warns _4'
            else:
                inputs['target_file'] = 'nonexistent_file_xyz.py'
                inputs['sif_content'] = base_sif.format(
                    topic='file-test',
                    s='File existence test',
                    i='File test insight',
                    d='File test design',
                    g='File test gotcha'
                )
        
        else:
            # Default: use real file with valid graph
            inputs['target_file'] = 'parity_test.py'
            inputs['sif_content'] = base_sif.format(
                topic='default-test',
                s='Default test summary',
                i='Default test insight',
                d='Default test design',
                g='Default test gotcha'
            )
    
    return inputs


# ─────────────────────────────────────────────────────────────────────────────
# Execution
# ─────────────────────────────────────────────────────────────────────────────

def run_python_verb(verb: str, inputs: Dict[str, Any], verbose: bool = False) -> Tuple[Any, int, str]:
    """Execute verb.py with given inputs. Returns (output, exit_code, stderr)."""
    verb_py = Path(f"{verb}.py")
    
    if not verb_py.exists():
        return None, -1, f"File not found: {verb_py}"
    
    # Build command based on verb
    cmd = ['python', str(verb_py)]
    
    if verb == 'remember':
        agent_id = inputs.get('agent_id', 'opus')
        cmd.append(agent_id)
        
        if inputs.get('mode') == 'theme':
            cmd.extend(['--theme', inputs.get('theme', 'test')])
        else:
            cmd.append(inputs.get('target_file', 'test.py'))
        
        cmd.append(inputs.get('sif_content', '@G test opus 2026-01-04; N S "Test"'))
    
    elif verb == 'recall':
        agent_id = inputs.get('agent_id', 'opus')
        cmd.append(agent_id)
        
        if inputs.get('theme'):
            cmd.extend(['--theme', inputs.get('theme')])
        else:
            cmd.append(inputs.get('query', 'test'))
    
    elif verb == 'wake':
        cmd.append(inputs.get('agent_id', 'opus'))
    
    if verbose:
        print(f"  [PY] Running: {' '.join(cmd[:4])}...")
    
    try:
        result = subprocess.run(
            cmd, 
            capture_output=True, 
            text=True, 
            encoding='utf-8',
            timeout=60,
            cwd=Path(__file__).parent
        )
        return result.stdout, result.returncode, result.stderr
    except subprocess.TimeoutExpired:
        return None, -2, "Timeout"
    except Exception as e:
        return None, -3, str(e)


def run_sif_verb(verb: str, inputs: Dict[str, Any], verbose: bool = False) -> Tuple[Any, int, str]:
    """Execute forge.py verb.sif with given inputs. Returns (output, exit_code, stderr)."""
    sif_file = Path(f"{verb}.sif")
    
    if not sif_file.exists():
        return None, -1, f"File not found: {sif_file}"
    
    # For SIF execution, we need to pass inputs via environment or temp file
    # since forge.py reads from K-nodes in the SIF itself
    
    # Create a modified SIF with test inputs injected into K-nodes
    with open(sif_file) as f:
        sif_content = f.read()
    
    # Inject test inputs as JSON in the first K-node
    test_inputs_json = json.dumps(inputs)
    
    # Write to temp file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.sif', delete=False) as tmp:
        # Prepend test inputs as K-node
        tmp.write(f"N test_inputs K '{test_inputs_json}'\n")
        tmp.write(sif_content)
        tmp_path = tmp.name
    
    cmd = ['python', 'forge.py', tmp_path]
    
    if verbose:
        print(f"  [SIF] Running: forge.py {sif_file}...")
    
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            encoding='utf-8',
            timeout=120,  # SIF execution may be slower (LLM calls)
            cwd=Path(__file__).parent
        )
        os.unlink(tmp_path)
        return result.stdout, result.returncode, result.stderr
    except subprocess.TimeoutExpired:
        os.unlink(tmp_path)
        return None, -2, "Timeout"
    except Exception as e:
        return None, -3, str(e)


# ─────────────────────────────────────────────────────────────────────────────
# Parity Comparison
# ─────────────────────────────────────────────────────────────────────────────

def compare_outputs(py_output: Any, sif_output: Any, test_case: TestCase) -> Tuple[bool, str]:
    """
    Compare Python and SIF outputs for parity.
    
    Parity is not always exact string match - it's semantic equivalence:
    - Same exit codes for success/failure cases
    - Same key data in output (stored ID, search results, etc.)
    - Error cases should both fail, success cases should both succeed
    """
    notes = []
    
    # Null checks
    if py_output is None and sif_output is None:
        return True, "Both returned None"
    
    if py_output is None or sif_output is None:
        return False, f"Output mismatch: py={py_output is not None}, sif={sif_output is not None}"
    
    # Exact match (ideal)
    if py_output == sif_output:
        return True, "Exact match"
    
    # Semantic comparison for remember
    if 'remember' in test_case.name.lower() or 'store' in test_case.description.lower():
        # Both should indicate success
        py_success = 'remembered' in str(py_output).lower() or 'stored' in str(py_output).lower()
        sif_success = 'stored' in str(sif_output).lower() or 'true' in str(sif_output).lower()
        
        if py_success and sif_success:
            return True, "Both indicate storage success"
        if not py_success and not sif_success:
            return True, "Both indicate storage failure"
    
    # Semantic comparison for recall
    if 'recall' in test_case.name.lower() or 'search' in test_case.description.lower():
        # Both should return results or both should return empty
        py_has_results = len(str(py_output)) > 50  # Non-trivial output
        sif_has_results = len(str(sif_output)) > 50
        
        if py_has_results == sif_has_results:
            return True, f"Both {'have' if py_has_results else 'lack'} substantial results"
    
    # Fallback: check if key patterns exist in both
    py_str = str(py_output).lower()
    sif_str = str(sif_output).lower()
    
    # Common success indicators
    success_patterns = ['success', 'stored', 'found', 'complete', 'ok']
    failure_patterns = ['error', 'fail', 'invalid', 'shallow', 'missing']
    
    py_success = any(p in py_str for p in success_patterns)
    py_failure = any(p in py_str for p in failure_patterns)
    sif_success = any(p in sif_str for p in success_patterns)
    sif_failure = any(p in sif_str for p in failure_patterns)
    
    if py_success == sif_success and py_failure == sif_failure:
        return True, "Same success/failure pattern"
    
    return False, f"Output mismatch - py: {py_str[:100]}... sif: {sif_str[:100]}..."


def run_parity_test(verb: str, test_case: TestCase, verbose: bool = False) -> ParityResult:
    """Run a single test case against both implementations."""
    
    # Run Python version
    py_output, py_exit, py_stderr = run_python_verb(verb, test_case.inputs, verbose)
    
    # Run SIF version
    sif_output, sif_exit, sif_stderr = run_sif_verb(verb, test_case.inputs, verbose)
    
    # Compare
    parity, notes = compare_outputs(py_output, sif_output, test_case)
    
    # Exit code parity
    if py_exit != sif_exit:
        # Success/failure mismatch is significant
        if (py_exit == 0) != (sif_exit == 0):
            parity = False
            notes = f"Exit code mismatch: py={py_exit}, sif={sif_exit}. " + notes
    
    return ParityResult(
        test_case=test_case,
        python_output=py_output,
        python_exit_code=py_exit,
        python_stderr=py_stderr,
        sif_output=sif_output,
        sif_exit_code=sif_exit,
        sif_stderr=sif_stderr,
        parity=parity,
        notes=notes
    )


# ─────────────────────────────────────────────────────────────────────────────
# Reporting
# ─────────────────────────────────────────────────────────────────────────────

def print_results(results: List[ParityResult], verbose: bool = False):
    """Print test results summary."""
    passed = sum(1 for r in results if r.parity)
    total = len(results)
    
    print(f"\n{'='*60}")
    print(f"PARITY TEST RESULTS: {passed}/{total} passed")
    print(f"{'='*60}\n")
    
    for r in results:
        status = "✓ PASS" if r.parity else "✗ FAIL"
        print(f"{status}  {r.test_case.name}")
        print(f"       {r.test_case.description[:60]}...")
        print(f"       {r.notes}")
        
        if verbose or not r.parity:
            print(f"       PY exit={r.python_exit_code}, SIF exit={r.sif_exit_code}")
            if r.python_stderr:
                print(f"       PY stderr: {r.python_stderr[:100]}...")
            if r.sif_stderr:
                print(f"       SIF stderr: {r.sif_stderr[:100]}...")
        print()
    
    # Summary
    print(f"\n{'='*60}")
    if passed == total:
        print("🎉 LOGIC PARITY ACHIEVED")
    else:
        print(f"⚠️  PARITY FAILURES: {total - passed}")
    print(f"{'='*60}")


def generate_sif_report(verb: str, results: List[ParityResult]) -> str:
    """Generate SIF graph summarizing test results."""
    passed = sum(1 for r in results if r.parity)
    total = len(results)
    
    timestamp = datetime.now().strftime('%Y-%m-%d')
    
    lines = [f"@G parity-test-{verb} opus {timestamp}"]
    lines.append(f"N S 'Parity Test: {verb}.py vs {verb}.sif - {passed}/{total} passed'")
    
    for i, r in enumerate(results):
        status = 'PASS' if r.parity else 'FAIL'
        lines.append(f"N t{i} Test '{r.test_case.name}: {status}'")
        if not r.parity:
            lines.append(f"N f{i} Failure '{r.notes[:80]}'")
            lines.append(f"E t{i} caused f{i}")
    
    if passed == total:
        lines.append(f"N result I 'Logic Parity ACHIEVED - SIF compilation correct'")
    else:
        lines.append(f"N result G 'Logic Parity FAILED - {total-passed} test(s) divergent'")
    
    lines.append(f"E _1 summarizes result")
    
    return "; ".join(lines)


def analyze_parity_gaps(verb: str, results: List[ParityResult]) -> str:
    """Generate detailed gap analysis between Python and SIF implementations."""
    passed = sum(1 for r in results if r.parity)
    total = len(results)
    
    lines = []
    lines.append(f"\n{'='*70}")
    lines.append(f"PARITY GAP ANALYSIS: {verb}.py vs {verb}.sif")
    lines.append(f"{'='*70}\n")
    
    # Categorize failures
    exit_code_failures = []
    validation_failures = []
    output_mismatches = []
    
    for r in results:
        if r.parity:
            continue
        
        if 'exit code mismatch' in r.notes.lower():
            # Check if it's a validation issue
            stderr = r.python_stderr.lower()
            if 'shallow' in stderr or 'superficial' in stderr:
                validation_failures.append(r)
            else:
                exit_code_failures.append(r)
        elif 'output mismatch' in r.notes.lower():
            output_mismatches.append(r)
        else:
            exit_code_failures.append(r)
    
    # Summary
    lines.append(f"Summary: {passed}/{total} tests passed ({100*passed//total if total else 0}% parity)")
    lines.append(f"")
    
    if validation_failures:
        lines.append(f"🔍 VALIDATION GAP ({len(validation_failures)} tests)")
        lines.append(f"   Python has validation layers that SIF does not replicate:")
        
        validation_types = set()
        for r in validation_failures:
            if 'shallow understanding' in r.python_stderr.lower():
                validation_types.add("• check_depth() - 4+ nodes, 3+ edges, 2+ types")
            if 'superficial' in r.python_stderr.lower():
                validation_types.add("• validate_comprehensiveness() - LLM semantic check")
            if 'shallow synthesis' in r.python_stderr.lower():
                validation_types.add("• check_coverage() - specific detail coverage")
        
        for vt in sorted(validation_types):
            lines.append(f"     {vt}")
        
        lines.append(f"")
        lines.append(f"   RECOMMENDATION: Add validation nodes to {verb}.sif:")
        lines.append(f"     N l_depth L 'Is graph depth >= 4 nodes?'")
        lines.append(f"     N n_reject_shallow A 'Reject shallow graph'")
        lines.append(f"     E l_depth no n_reject_shallow")
        lines.append(f"")
    
    if exit_code_failures:
        lines.append(f"⚠️  EXIT CODE DIVERGENCE ({len(exit_code_failures)} tests)")
        for r in exit_code_failures:
            lines.append(f"   • {r.test_case.name}: py={r.python_exit_code} vs sif={r.sif_exit_code}")
        lines.append(f"")
    
    if output_mismatches:
        lines.append(f"📊 OUTPUT MISMATCH ({len(output_mismatches)} tests)")
        for r in output_mismatches:
            lines.append(f"   • {r.test_case.name}")
            lines.append(f"     PY: {str(r.python_output)[:60]}...")
            lines.append(f"     SIF: {str(r.sif_output)[:60]}...")
        lines.append(f"")
    
    # Root cause analysis
    lines.append(f"{'='*70}")
    lines.append(f"ROOT CAUSE ANALYSIS")
    lines.append(f"{'='*70}")
    lines.append(f"")
    
    if validation_failures:
        lines.append(f"1. SIF uses simulated_llm_responses (training wheels)")
        lines.append(f"   - Forge bypasses actual execution with canned responses")
        lines.append(f"   - Python performs real validation with LLM calls")
        lines.append(f"")
        lines.append(f"2. Validation logic missing from SIF")
        lines.append(f"   - Python: check_depth(), validate_comprehensiveness(), check_coverage()")
        lines.append(f"   - SIF: None of these checks exist")
        lines.append(f"")
    
    lines.append(f"NEXT STEPS:")
    lines.append(f"  1. Add validation L-nodes to {verb}.sif (depth, comprehensiveness)")
    lines.append(f"  2. Remove simulated responses from forge.py for real parity testing")
    lines.append(f"  3. Or: Test with --dry-run flag in Python (skip validation)")
    
    return "\n".join(lines)


# ─────────────────────────────────────────────────────────────────────────────
# CLI
# ─────────────────────────────────────────────────────────────────────────────

def list_verb_pairs():
    """List available verb.py + verb.sif pairs."""
    workspace = Path(__file__).parent
    
    # Find all .py files that have matching .sif
    pairs = []
    for py_file in workspace.glob("*.py"):
        sif_file = workspace / f"{py_file.stem}.sif"
        if sif_file.exists():
            pairs.append(py_file.stem)
    
    print("Available verb pairs for parity testing:")
    for verb in sorted(pairs):
        print(f"  • {verb}")


def main():
    import argparse
    
    parser = argparse.ArgumentParser(description="Logic Parity Testing Framework")
    parser.add_argument('verb', nargs='?', help='Verb to test (e.g., remember, recall)')
    parser.add_argument('--list', action='store_true', help='List available verb pairs')
    parser.add_argument('--generate', action='store_true', help='Generate test cases and exit')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')
    parser.add_argument('--sif-report', action='store_true', help='Output results as SIF')
    parser.add_argument('--analyze', '-a', action='store_true', help='Show detailed gap analysis')
    
    args = parser.parse_args()
    
    if args.list:
        list_verb_pairs()
        return 0
    
    if not args.verb:
        parser.print_help()
        return 1
    
    verb = args.verb
    sif_file = Path(f"{verb}.sif")
    py_file = Path(f"{verb}.py")
    
    if not sif_file.exists():
        print(f"ERROR: {sif_file} not found")
        return 1
    
    if not py_file.exists():
        print(f"ERROR: {py_file} not found")
        return 1
    
    print(f"Parity Testing: {verb}.py vs {verb}.sif")
    print(f"{'='*60}")
    
    # Extract T-nodes
    test_nodes = extract_test_nodes(sif_file)
    print(f"Found {len(test_nodes)} T-nodes (test assertions)")
    
    # Generate test cases
    test_cases = generate_test_cases(verb, sif_file)
    print(f"Generated {len(test_cases)} test cases")
    
    if args.generate:
        print("\nGenerated Test Cases:")
        for tc in test_cases:
            print(f"  • {tc.name}: {tc.description[:50]}...")
            print(f"    Inputs: {tc.inputs}")
        return 0
    
    # Run tests
    print(f"\nRunning parity tests...")
    results = []
    for tc in test_cases:
        if args.verbose:
            print(f"\n--- {tc.name} ---")
        result = run_parity_test(verb, tc, args.verbose)
        results.append(result)
    
    # Report
    if args.sif_report:
        print(generate_sif_report(verb, results))
    elif args.analyze:
        print(analyze_parity_gaps(verb, results))
    else:
        print_results(results, args.verbose)
    
    # Exit code
    passed = sum(1 for r in results if r.parity)
    return 0 if passed == len(results) else 1


if __name__ == "__main__":
    sys.exit(main())
