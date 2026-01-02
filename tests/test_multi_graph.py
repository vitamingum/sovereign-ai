#!/usr/bin/env python3
"""
Test for multi-graph reconstruction in recollect.py

When multiple SIF graphs are stored for the same file, recollect
should properly reconstruct them without node ID collisions.
"""

import unittest
import os
import sys
import tempfile
import shutil
from pathlib import Path

# Add parent to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from enclave.semantic_memory import SemanticMemory
from enclave.sif_parser import SIFParser
from remember import store_understanding, parse_sif_understanding
from recollect import reconstruct_graph


class TestMultiGraphReconstruction(unittest.TestCase):
    """Test that multiple graphs for same file reconstruct correctly."""
    
    def setUp(self):
        """Create a fresh temporary enclave for each test."""
        self.temp_dir = tempfile.mkdtemp(prefix="test_enclave_")
        self.enclave_path = Path(self.temp_dir)
        
        # Create storage structure
        (self.enclave_path / "storage" / "private").mkdir(parents=True)
        (self.enclave_path / "storage" / "public").mkdir(parents=True)
        
        # Create a test target file
        self.test_file = self.enclave_path / "test_target.py"
        self.test_file.write_text("# Test file\nprint('hello')\n")
        
        # Initialize memory with test passphrase
        self.mem = SemanticMemory(str(self.enclave_path))
        self.mem.unlock("test_passphrase_12345")
    
    def tearDown(self):
        """Clean up temporary directory."""
        shutil.rmtree(self.temp_dir, ignore_errors=True)
    
    def test_single_graph_reconstruction(self):
        """Single graph should reconstruct with correct node IDs."""
        sif_text = """@G test-graph-alpha opus 2026-01-02
N n1 Component 'AlphaComponent - does alpha things'
N n2 Method 'process() handles the main logic'
N n3 Design 'Uses strategy pattern for flexibility'
E n1 contains n2
E n3 implements n1"""
        
        graph = SIFParser.parse(sif_text)
        store_understanding(self.mem, graph, str(self.test_file))
        
        # Retrieve using multiple queries to get all node types
        # Semantic search needs different queries for different types
        all_results = []
        for query in ["[Component]", "[Method]", "[Design]", "[Anchor]", "test_target.py"]:
            results = self.mem.recall_similar(query, top_k=50, threshold=0.1)
            all_results.extend(results)
        
        # Deduplicate by memory id
        seen_ids = set()
        relevant = []
        for r in all_results:
            if r['id'] not in seen_ids and "test_target.py" in r.get('metadata', {}).get('target_path', ''):
                seen_ids.add(r['id'])
                relevant.append(r)
        
        reconstructed = reconstruct_graph(relevant)
        
        # Check nodes are present
        node_ids = [n['id'] for n in reconstructed['nodes']]
        self.assertIn('n1', node_ids, f"n1 not found in {node_ids}")
        self.assertIn('n2', node_ids, f"n2 not found in {node_ids}")
        self.assertIn('n3', node_ids, f"n3 not found in {node_ids}")
        
        # Check edges reference correct nodes
        edge_sources = [e[0] for e in reconstructed['edges']]
        edge_targets = [e[2] for e in reconstructed['edges']]
        for src in edge_sources:
            self.assertIn(src, node_ids, f"Edge source {src} not in nodes")
        for tgt in edge_targets:
            if not tgt.startswith('anchor_'):
                self.assertIn(tgt, node_ids, f"Edge target {tgt} not in nodes")
    
    def test_multi_graph_node_isolation(self):
        """Multiple graphs should have isolated node namespaces."""
        # Store first graph
        sif_alpha = """@G graph-alpha opus 2026-01-02
N n1 Component 'AlphaMain - primary alpha component'
N n2 Method 'alpha_process() does alpha work'
E n1 contains n2"""
        
        graph_alpha = SIFParser.parse(sif_alpha)
        store_understanding(self.mem, graph_alpha, str(self.test_file))
        
        # Store second graph with SAME node IDs but different content
        sif_beta = """@G graph-beta opus 2026-01-02
N n1 Component 'BetaMain - primary beta component'
N n2 Method 'beta_process() does beta work'
E n1 contains n2"""
        
        graph_beta = SIFParser.parse(sif_beta)
        store_understanding(self.mem, graph_beta, str(self.test_file))
        
        # Retrieve all memories for this file
        results = self.mem.recall_similar("[Component] test_target.py", top_k=100, threshold=0.1)
        relevant = [r for r in results if "test_target.py" in r.get('metadata', {}).get('target_path', '')]
        
        reconstructed = reconstruct_graph(relevant)
        
        # BUG CHECK: The real issue is edges - both graphs have "n1 uses n2"
        # but after merge, we can't tell which n2 belongs to which graph
        
        # Count nodes by ID - should have proper namespacing
        node_ids = [n['id'] for n in reconstructed['nodes']]
        
        # With proper namespacing, we'd have graph-alpha:n1, graph-alpha:n2, etc.
        # Current bug: we have multiple 'n1' entries, multiple 'n2' entries
        # which causes edge confusion
        
        # Check that we don't have duplicate IDs pointing to different content
        id_to_contents = {}
        for n in reconstructed['nodes']:
            nid = n['id']
            if nid not in id_to_contents:
                id_to_contents[nid] = set()
            id_to_contents[nid].add(n['content'])
        
        # If there's a bug, same ID maps to multiple different contents
        for nid, contents in id_to_contents.items():
            self.assertEqual(len(contents), 1,
                f"Node ID '{nid}' has multiple different contents: {contents}\n"
                f"This indicates node ID collision between graphs.")
    
    def test_multi_graph_edge_integrity(self):
        """Edges should point to correct nodes after multi-graph merge."""
        # Store first graph
        sif_one = """@G graph-one opus 2026-01-02
N n1 Component 'OneComponent'
N n2 Helper 'OneHelper'
E n1 uses n2"""
        
        graph_one = SIFParser.parse(sif_one)
        store_understanding(self.mem, graph_one, str(self.test_file))
        
        # Store second graph - n2 here is DIFFERENT from n2 above
        sif_two = """@G graph-two opus 2026-01-02
N n1 Component 'TwoComponent'
N n2 Helper 'TwoHelper'
E n1 uses n2"""
        
        graph_two = SIFParser.parse(sif_two)
        store_understanding(self.mem, graph_two, str(self.test_file))
        
        # Retrieve and check
        results = self.mem.recall_similar("[Component] test_target.py", top_k=100, threshold=0.1)
        relevant = [r for r in results if "test_target.py" in r.get('metadata', {}).get('target_path', '')]
        
        reconstructed = reconstruct_graph(relevant)
        
        # Build a map of node_id -> content for verification
        node_map = {n['id']: n['content'] for n in reconstructed['nodes']}
        
        # Check edge integrity: each edge should connect related nodes
        # BUG: Without graph namespacing, edge from "graph-one" n1->n2 
        # might now point to "graph-two"'s n2
        for src, rel, tgt in reconstructed['edges']:
            if tgt.startswith('anchor_'):
                continue
            
            src_content = node_map.get(src, '')
            tgt_content = node_map.get(tgt, '')
            
            # If source is "OneComponent", target should be "OneHelper"
            # If source is "TwoComponent", target should be "TwoHelper"
            if 'OneComponent' in src_content:
                self.assertIn('OneHelper', tgt_content,
                    f"Edge from OneComponent points to {tgt_content}, not OneHelper")
            elif 'TwoComponent' in src_content:
                self.assertIn('TwoHelper', tgt_content,
                    f"Edge from TwoComponent points to {tgt_content}, not TwoHelper")


class TestGraphIdPreservation(unittest.TestCase):
    """Test that graph_id is properly tracked during reconstruction."""
    
    @classmethod
    def setUpClass(cls):
        """Create a temporary enclave for testing."""
        cls.temp_dir = tempfile.mkdtemp(prefix="test_enclave_gid_")
        cls.enclave_path = Path(cls.temp_dir)
        
        (cls.enclave_path / "storage" / "private").mkdir(parents=True)
        (cls.enclave_path / "storage" / "public").mkdir(parents=True)
        
        cls.test_file = cls.enclave_path / "gid_target.py"
        cls.test_file.write_text("# Graph ID test file\n")
        
        cls.mem = SemanticMemory(str(cls.enclave_path))
        cls.mem.unlock("test_passphrase_gid_12345")
    
    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.temp_dir, ignore_errors=True)
    
    def test_graph_id_in_metadata(self):
        """Each memory should have its graph_id preserved."""
        sif_text = """@G unique-graph-id-xyz opus 2026-01-02
N n1 Component 'TestComponent'
E n1 anchored_to anchor"""
        
        graph = SIFParser.parse(sif_text)
        store_understanding(self.mem, graph, str(self.test_file))
        
        results = self.mem.recall_similar("[Component] gid_target.py", top_k=50, threshold=0.1)
        relevant = [r for r in results if "gid_target.py" in r.get('metadata', {}).get('target_path', '')]
        
        # Check that graph_id is preserved
        for mem in relevant:
            meta = mem.get('metadata', {})
            if meta.get('node_type') != 'Anchor':
                self.assertEqual(meta.get('graph_id'), 'unique-graph-id-xyz',
                    f"graph_id not preserved: {meta.get('graph_id')}")


if __name__ == "__main__":
    unittest.main(verbosity=2)
