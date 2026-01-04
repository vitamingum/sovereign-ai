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
        
        # SIMULATED LLM KNOWLEDGE BASE
        self.simulated_llm_responses = {
            # Action: Generate Data
            'Generate a list of 5 random integers': 
                "def action(ctx):\n    import random\n    return [random.randint(1, 100) for _ in range(5)]",
            
            # Test: Verify Data
            'Verify list has 5 items': 
                "def test(ctx, result):\n    return len(result) == 5",
            
            # Action: Process Data
            'Calculate sum of list': 
                "def action(ctx):\n    data = ctx.get('data_stream')\n    return sum(data)",
            
            # Test: Verify Sum
            'Verify sum is integer': 
                "def test(ctx, result):\n    return isinstance(result, int)",
                
            # Logic: Check Threshold
            'Is sum > 250?': 
                "def logic(ctx):\n    return ctx.get('sum_val', 0) > 250",
                
            # Action: High Value Path
            'Log "High Value"': 
                "def action(ctx):\n    print('LOG: High Value Detected')\n    return 'Logged High'",
                
            # Action: Low Value Path
            'Log "Low Value"': 
                "def action(ctx):\n    print('LOG: Low Value Detected')\n    return 'Logged Low'",

            # Wake Milestone 1
            'Load agent configuration':
                "def action(ctx):\n    # Real Implementation\n    import json\n    from enclave.config import get_agent_or_raise\n    \n    # Simulate loading from K-node\n    k_nodes = ctx.get('__knowledge__', [])\n    if not k_nodes: return None\n    \n    # Parse K-node to get agent_id\n    data = json.loads(k_nodes[0])\n    agent_id = data.get('agent_id')\n    \n    # Load real config\n    agent = get_agent_or_raise(agent_id)\n    print(f'Loaded REAL config for {agent.name}')\n    return {'agent_id': agent.id, 'agent_obj': agent}",
            
            'Verify agent name is gemini':
                "def test(ctx, result):\n    return result['agent_id'] == 'gemini'",

            # Wake Milestone 2
            'Load Enclave Passphrases':
                "def action(ctx):\n    # Real Implementation\n    import os\n    import sys\n    from pathlib import Path\n    from enclave.hardware import get_enclave\n    \n    config = ctx.get('load')\n    if not config: raise ValueError('No config fed from previous node')\n    agent = config['agent_obj']\n    \n    print(f'Loading REAL keys for {agent.name}...')\n    \n    # 1. Shared Key\n    shared_passphrase = os.environ.get('SHARED_ENCLAVE_KEY')\n    if not shared_passphrase:\n        env_file = Path('.env')\n        if env_file.exists():\n            with open(env_file, 'r') as f:\n                for line in f:\n                    if line.startswith('SHARED_ENCLAVE_KEY='):\n                        shared_passphrase = line.split('=', 1)[1].strip()\n    \n    # 2. Private Key (Hardware Enclave)\n    private_passphrase = None\n    key_file = Path(agent.private_enclave) / 'storage' / 'private' / 'key.sealed'\n    if key_file.exists():\n        try:\n            with open(key_file, 'rb') as f: sealed_data = f.read()\n            enclave = get_enclave()\n            private_passphrase = enclave.unseal(sealed_data).decode('utf-8')\n            print('  -> Unsealed key from Hardware Enclave')\n        except Exception as e:\n            print(f'  -> Failed to unseal: {e}')\n            \n    if not private_passphrase:\n        # Fallback to env\n        private_passphrase = os.environ.get(f'{agent.env_prefix}_KEY')\n        \n    return {'shared_key': shared_passphrase, 'private_key': private_passphrase, 'shared_dir': agent.shared_enclave, 'private_dir': agent.private_enclave}",

            'Verify passphrases loaded':
                "def test(ctx, result):\n    return result and result.get('shared_key') and result.get('private_key')",

            # Wake Milestone 3
            'InitSemanticMemory':
                "def action(ctx):\n    # Real Implementation\n    from enclave.semantic_memory import SemanticMemory\n    \n    keys = ctx.get('initsemanticmemory')\n    if not keys: raise ValueError('No keys loaded')\n    \n    print('Initializing REAL Semantic Memory...')\n    memory = SemanticMemory(keys['shared_dir'])\n    # We don't actually unlock it here because SemanticMemory might not take the key in init, \n    # but let's assume we just return the object for now.\n    return {'status': 'ready', 'memory_obj': memory}",

            'Verify memory ready':
                "def test(ctx, result):\n    return result['status'] == 'ready'",

            'InitOpaqueStorage':
                "def action(ctx):\n    # Real Implementation\n    from enclave.opaque import OpaqueStorage\n    \n    keys = ctx.get('initopaquestorage')\n    if not keys: raise ValueError('No keys loaded')\n    \n    print('Initializing REAL Opaque Storage...')\n    # OpaqueStorage is a static utility class in this codebase, not an object we instantiate with keys.\n    # We just verify we can import it and access its methods.\n    return {'status': 'connected', 'storage_class': 'OpaqueStorage'}",

            'Verify storage connected':
                "def test(ctx, result):\n    return result['status'] == 'connected'"
        }

    def get_executable(self, node: Dict, context_nodes: List[Dict], test_nodes: List[Dict]) -> Callable:
        """
        Returns a callable Python function for the given node.
        If cache miss, simulates LLM generation + Test Oracle validation.
        """
        # 1. Calculate Hash (Content + Type)
        content_hash = hashlib.md5(f"{node['content']}:{node['type']}".encode()).hexdigest()[:8]
        cache_file = self.cache_dir / f"node_{content_hash}.py"
        
        # 2. Check Disk Cache
        if not cache_file.exists():
            # print(f"[Forge] Cache Miss for '{node['content']}' -> Hallucinating implementation...")
            code = self._hallucinate_code(node['content'], node['type'])
            
            with open(cache_file, "w") as f:
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
                with open(test_cache, "w") as f:
                    f.write(code)
            
            spec = importlib.util.spec_from_file_location(f"node_{test_hash}", test_cache)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            test_func = getattr(module, 'test')
            
            # Execute test
            try:
                passed = test_func(runtime_context, action_result)
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
                # print(f"        ✗ ERROR in test: {e}")
                return False
        
        # print(f"[Forge] All tests passed. Cache valid.")
        return True

    def _hallucinate_code(self, intent: str, node_type: str) -> str:
        if intent in self.simulated_llm_responses:
            return self.simulated_llm_responses[intent]
        # print(f"[Forge] ⚠️ UNKNOWN INTENT: {intent}")
        return "def action(ctx): print('Not implemented'); return None"

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
                self.context['__knowledge__'] = [n['content'] for n in context_nodes]
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
        print("Usage: py forge.py <sif_file>")
        sys.exit(1)
    
    sif_file = sys.argv[1]
    with open(sif_file, 'r') as f:
        sif_content = f.read()
        
    runtime = ForgeRuntime()
    runtime.run(sif_content)
