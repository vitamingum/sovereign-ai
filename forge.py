#!/usr/bin/env python3
"""
forge.py - The SIF Runtime v2 (Robust Execution).

Executes SIF graphs as code by JIT-compiling nodes to Python via an LLM (simulated).
Implements Strict Node Typing (A/K/T), Edge Semantics, and Test Oracles.
"""

import sys
import os
import json
import hashlib
import importlib.util
from typing import Dict, Any, Callable, List, Optional
from pathlib import Path

# Add workspace root to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.sif_parser import SIFParser
from enclave.llm import LocalLLM

# ─────────────────────────────────────────────────────────────────────────────
# Cognitive Cache (The "Memory" of the Runtime)
# ─────────────────────────────────────────────────────────────────────────────

class CognitiveCache:
    """
    Manages the mapping between SIF Node Intents and Executable Python Code.
    """
    def __init__(self):
        self.cache_dir = Path(".forge/cache")
        self.cache_dir.mkdir(parents=True, exist_ok=True)
        
        # BOOTSTRAP KNOWLEDGE BASE (Removed - Compiler Only)
        # Previously contained hardcoded implementations. 
        # Now relying 100% on JIT compilation via DeepSeek/Qwen.


    def get_executable(self, node: Dict, context_nodes: List[Dict], test_nodes: List[Dict]) -> Callable:
        """
        Returns a callable Python function for the given node.
        If cache miss, simulates LLM generation + Test Oracle validation.
        """
        # 1. Calculate Hash (Content + Type + Context)
        # We include context_nodes in hash because they might contain API signatures that change the generated code
        context_str = "".join(sorted([n['content'] for n in context_nodes]))
        content_hash = hashlib.md5(f"{node['content']}:{node['type']}:{context_str}".encode()).hexdigest()[:8]
        cache_file = self.cache_dir / f"node_{content_hash}.py"
        
        # 2. Check Disk Cache
        if not cache_file.exists():
            # print(f"[Forge] Cache Miss for '{node['content']}' -> Hallucinating implementation...")
            code = self._hallucinate_code(node['content'], node['type'], context_nodes)
            
            with open(cache_file, "w", encoding='utf-8') as f:
                f.write(code)
        else:
            # print(f"[Forge] Cache Hit for '{node['content']}'")
            pass

        # 3. Load Module
        try:
            spec = importlib.util.spec_from_file_location(f"node_{content_hash}", cache_file)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
        except Exception as e:
            # print(f"[Forge] ❌ Failed to load module: {e}")
            if cache_file.exists(): os.remove(cache_file)
            raise

        # 4. Return Wrapper that runs Tests
        def executable_wrapper(ctx):
            # Get the raw function
            if node['type'] == 'Logic':
                func = getattr(module, 'logic')
            elif node['type'] == 'Test':
                func = getattr(module, 'test')
            else:
                func = getattr(module, 'action')
            
            # Execute
            result = func(ctx)
            
            # Run Test Oracles (if any)
            if test_nodes and node['type'] == 'Action':
                # We need to pass the cache_file to run_test_oracles so it can delete it on failure
                if not self.run_test_oracles(result, test_nodes, ctx, cache_file):
                    raise RuntimeError(f"Test Oracle Failed for '{node['content']}'")
            
            return result

        return executable_wrapper
    
    def run_test_oracles(self, action_result: Any, test_nodes: List[Dict], 
                         runtime_context: Dict, cache_file: Path) -> bool:
        """
        Execute test oracles against an action result.
        Returns True if all pass, False if any fail.
        On failure, deletes the cached code.
        """
        if not test_nodes:
            return True
            
        # print(f"[Forge] Running {len(test_nodes)} Test Oracle(s)...")
        
        for test_node in test_nodes:
            # Get test executable
            test_hash = hashlib.md5(f"{test_node['content']}:Test".encode()).hexdigest()[:8]
            test_cache = self.cache_dir / f"node_{test_hash}.py"
            
            if not test_cache.exists():
                code = self._hallucinate_code(test_node['content'], 'Test')
                with open(test_cache, "w", encoding='utf-8') as f:
                    f.write(code)
            
            spec = importlib.util.spec_from_file_location(f"node_{test_hash}", test_cache)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            test_func = getattr(module, 'test')
            
            # Execute test
            try:
                print(f"        DEBUG: Testing with action_result={action_result}, ctx_keys={list(runtime_context.keys())}")
                passed = test_func(runtime_context, action_result)
                print(f"        DEBUG: Test returned {passed}")
                if passed:
                    # print(f"        ✓ {test_node['content']}")
                    pass
                else:
                    # print(f"        ✗ FAILED: {test_node['content']}")
                    # Delete bad cached code
                    if cache_file.exists():
                        cache_file.unlink()
                        # print(f"[Forge] Deleted invalid cache: {cache_file.name}")
                    return False
            except Exception as e:
                print(f"        ✗ ERROR in test: {e}")
                return False
        
        # print(f"[Forge] All tests passed. Cache valid.")
        return True

    def _hallucinate_code(self, intent: str, node_type: str, context_nodes: List[Dict] = []) -> str:
        # Default to compilation, use bootstrap only on failure
        
        print(f"[Forge] JIT Compiling '{intent}'...")
        
        # Extract API Context from K-nodes
        api_context = ""
        for node in context_nodes:
            content = node.get('content', '')
            if "API:" in content:
                # Clean up API one-liners
                clean_content = content.replace("API:", "").strip()
                # If it contains semicolons, replace with newlines for better readability
                if ";" in clean_content:
                    clean_content = clean_content.replace("; #", "\n").replace(";", "\n")
                api_context += f"\n# From Knowledge Node:\n{clean_content}\n"
            elif "class " in content or "def " in content:
                api_context += f"\n{content}\n"
        
        if api_context:
            print(f"[Forge] API Context for '{intent}':\n{api_context}\n--------------------------------")
        
        try:
            print("[Forge] Initializing LLM (qwen2.5-coder:14b)...")
            # Use qwen-coder for faster compilation
            llm = LocalLLM(model="qwen2.5-coder:14b")
            
            print("[Forge] Constructing prompt...")
            prompt = f"""
            You are a Python Code Generator for the SIF Runtime.
            Your task is to generate a Python function that implements the following intent:
            
            Intent: "{intent}"
            Node Type: {node_type}
            
            Requirements:
            1. If Node Type is 'Action', generate a function named 'action(ctx)'.
               - 'ctx' is a dictionary containing the runtime state.
               - Input data (Knowledge nodes) is in ctx.get('__knowledge__', []).
                 It is a list of strings (often JSON).
               - Previous results are in ctx (e.g. ctx.get('theme'), ctx.get('agent_id')).
               
               *** IMPORTS MUST BE INSIDE THE FUNCTION ***
               Every function MUST start with all necessary imports (e.g., json, os, random).
               
               *** RESTRICTIONS ***
               - DO NOT import 'enclave' modules UNLESS they are explicitly shown in the API Context below.
               - DO NOT call functions you haven't defined or imported.
               - Stick to standard Python libraries (json, math, random, datetime) unless instructed otherwise.
               
               def action(ctx):
                   import json
                   # ... code ...
               
               *** API CONTEXT (MANDATORY) ***
               The following code snippets are available for you to use. 
               Integrate them into your function logic directly. 
               DO NOT check if 'api_context' is in ctx.
               ENSURE all variables used in the API calls are retrieved from 'ctx' first.
               
               {api_context}
               
               *** DATA FLOW STRATEGY ***
               1. Retrieve INPUT parameters from 'ctx'.
               2. If missing, retrieve from '__knowledge__' (parse JSON).
               3. If API CONTEXT is provided below, YOU MUST USE IT. Otherwise, implement standard logic.
               4. Return a dictionary with the result.
               
            2. If Node Type is 'Test', generate a function named 'test(ctx, result)'.
               - 'result' is the return value of the previous Action you are testing (usually a dict).
               - DO NOT assumption specific key names.
               - STRATEGY: Iterate over result.values() or look for keys containing relevant words (e.g. 'seq', 'list').
               - Return True if the test passes, False otherwise.
               
            3. If Node Type is 'Logic', generate a function named 'logic(ctx)'.
               - Return a boolean.
               
            4. OUTPUT ONLY THE PYTHON CODE. NO MARKDOWN. NO EXPLANATION.
            """
            print("[Forge] Prompt constructed successfully.")
            
            code = llm.generate(prompt)
            
            # Clean up code
            if "```python" in code:
                code = code.split("```python")[1].split("```")[0]
            elif "```" in code:
                code = code.split("```")[1].split("```")[0]
            
            code = code.strip()
            print(f"[Forge] Generated Code for '{intent}':\n{code}\n--------------------------------")
            return code
        except Exception as e:
            import traceback
            print(f"\n\n[Forge] ❌ CRITICAL LLM ERROR: {e}")
            traceback.print_exc()
            return "def action(ctx): print('LLM Generation Failed'); return None"

# ─────────────────────────────────────────────────────────────────────────────
# Forge Runtime v2 (The "CPU")
# ─────────────────────────────────────────────────────────────────────────────

class ForgeRuntime:
    def __init__(self):
        self.cache = CognitiveCache()
        self.context = {}  # Global state vector

    def run(self, sif_text: str):
        import datetime
        ts = datetime.datetime.now().isoformat()
        print(f"@G forge-trace-{ts.replace(':','-')} forge {ts}")
        
        graph = self._simple_parse(sif_text)
        
        if not graph['nodes']:
            print("N error Error 'Empty graph'")
            return
            
        # Find Start Node (First Action/Logic node)
        start_node = next((n for n in graph['nodes'] if n['type'] in ['Action', 'Logic']), None)
        if not start_node:
            print("N error Error 'No executable nodes found'")
            return
        current_node_id = start_node['id']
        
        steps = 0
        while current_node_id and steps < 20:
            node = next((n for n in graph['nodes'] if n['id'] == current_node_id), None)
            if not node: break
            
            # Skip non-executable nodes (Knowledge, Test are accessed via edges, not flow)
            if node['type'] in ['Knowledge', 'Test']:
                # print(f"[Forge] Skipping non-executable node {node['type']}")
                break

            step_id = f"step_{steps+1}"
            print(f"N {step_id} Execution 'Executed {node['id']}'")
            print(f"E {step_id} implements {node['id']}")
            
            # Gather Context (Knowledge nodes connected via 'feeds' or 'supports')
            # In v2, 'feeds' implies data flow, 'supports' implies prompt context
            context_nodes = self._get_connected_nodes(node['id'], graph, ['supports', 'requires'])
            if context_nodes:
                # Filter out API nodes from runtime knowledge to prevent JSON parse errors
                self.context['__knowledge__'] = [n['content'] for n in context_nodes 
                                               if not n['content'].strip().startswith('API:')]
            else:
                self.context['__knowledge__'] = []
                
            # Gather Tests (Test nodes connected via 'validates' or 'ensures')
            test_nodes = self._get_connected_nodes(node['id'], graph, ['validates', 'ensures'])
            
            # Execute
            func = self.cache.get_executable(node, context_nodes, test_nodes)
            try:
                result = func(self.context)
                # print(f"        Result: {result}")
                
                # Run Test Oracles (REAL execution, not simulated)
                if test_nodes:
                    content_hash = hashlib.md5(f"{node['content']}:{node['type']}".encode()).hexdigest()[:8]
                    cache_file = Path(".forge/cache") / f"node_{content_hash}.py"
                    if not self.cache.run_test_oracles(result, test_nodes, self.context, cache_file):
                        print(f"N fail_{steps} Failure 'Test Oracle Failed'")
                        print(f"E {step_id} resulted_in fail_{steps}")
                        break
                
                # Update State Vector via 'feeds' edges (dynamic, not hardcoded)
                feeds_edges = [e for e in graph['edges'] 
                              if e['source'] == node['id'] and e['relation'] == 'feeds']
                for edge in feeds_edges:
                    # Use target node ID as state key
                    target_node = next((n for n in graph['nodes'] if n['id'] == edge['target']), None)
                    if target_node:
                        # State key derived from target node content (first word) or ID
                        state_key = target_node['content'].split()[0].lower() if target_node['content'] else edge['target']
                        self.context[state_key] = result
                        # print(f"        → State['{state_key}'] = {result}")
                        print(f"N state_{steps}_{state_key} State 'Updated {state_key}'")
                        print(f"E {step_id} produced state_{steps}_{state_key}")
                
                # Also store by node ID for simple graphs
                self.context[f'result_{node["id"]}'] = result
                
                # MERGE RESULT INTO GLOBAL CONTEXT (Blackboard Pattern)
                if isinstance(result, dict):
                    self.context.update(result)
                    
            except Exception as e:
                print(f"N error_{steps} Error '{e}'")
                print(f"E {step_id} resulted_in error_{steps}")
                break
                
            # Navigate
            next_id = self._navigate(current_node_id, result, graph['edges'])
            if not next_id:
                # print("[Forge] End of flow.")
                pass
                break
                
            current_node_id = next_id
            steps += 1

    def _get_connected_nodes(self, node_id: str, graph: Dict, relations: List[str]) -> List[Dict]:
        """Finds nodes connected to the current node by specific relations."""
        connected = []
        for edge in graph['edges']:
            # Incoming edges (Knowledge -> supports -> Action)
            if edge['target'] == node_id and edge['relation'] in relations:
                source = next((n for n in graph['nodes'] if n['id'] == edge['source']), None)
                if source: connected.append(source)
            # Outgoing edges (Action -> ensures -> Test)
            if edge['source'] == node_id and edge['relation'] in relations:
                target = next((n for n in graph['nodes'] if n['id'] == edge['target']), None)
                if target: connected.append(target)
        return connected

    def _navigate(self, current_id: str, result: Any, edges: list) -> str:
        out_edges = [e for e in edges if e['source'] == current_id]
        
        # Logic Branching
        if isinstance(result, bool):
            relation = 'yes' if result else 'no'
            match = next((e for e in out_edges if e['relation'] == relation), None)
            if match: return match['target']
            
        # Sequential Flow (next or feeds)
        # Prefer 'next' for control flow, 'feeds' for data flow that also implies control
        match = next((e for e in out_edges if e['relation'] in ['next', 'feeds']), None)
        if match: return match['target']
        
        return None

    def _simple_parse(self, text: str) -> Dict:
        nodes = []
        edges = []
        lines = text.strip().split('\n')
        auto_id_counter = 0
        
        for line in lines:
            line = line.strip()
            if not line or line.startswith('#') or line.startswith('@G'): continue
            
            parts = line.split()
            kind = parts[0]
            
            if kind == 'N':
                # N Type 'Content'
                content_start = line.find("'")
                content_end = line.rfind("'")
                content = line[content_start+1:content_end]
                pre_content = line[:content_start].strip().split()
                
                if len(pre_content) == 2:
                    auto_id_counter += 1
                    nid = f"_{auto_id_counter}"
                    ntype = pre_content[1]
                else:
                    nid = pre_content[1]
                    ntype = pre_content[2]
                
                # Map v2 types
                if ntype == 'A': ntype = 'Action'
                if ntype == 'L': ntype = 'Logic'
                if ntype == 'K': ntype = 'Knowledge'
                if ntype == 'T': ntype = 'Test'
                
                nodes.append({'id': nid, 'type': ntype, 'content': content})
                
            elif kind == 'E':
                # E Source Relation Target
                edge_defs = line.split(';')
                for ed in edge_defs:
                    eparts = ed.strip().split()
                    if len(eparts) >= 4:
                        edges.append({'source': eparts[1], 'relation': eparts[2], 'target': eparts[3]})

        return {'nodes': nodes, 'edges': edges}

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: py forge.py <sif_file> [--knowledge '<json>']")
        sys.exit(1)
    
    sif_file = sys.argv[1]
    with open(sif_file, 'r', encoding='utf-8') as f:
        sif_content = f.read()
    
    # Parse optional --knowledge argument
    initial_knowledge = None
    if '--knowledge' in sys.argv:
        idx = sys.argv.index('--knowledge')
        if idx + 1 < len(sys.argv):
            initial_knowledge = sys.argv[idx + 1]
        
    runtime = ForgeRuntime()
    if initial_knowledge:
        runtime.context['__knowledge__'] = [initial_knowledge]
    runtime.run(sif_content)
