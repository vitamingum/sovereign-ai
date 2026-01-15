"""Tests for SIF compact format (@G/@N/@E syntax)."""

import unittest
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from lib_enclave.sif_parser import SIFParser

class TestSIFCompact(unittest.TestCase):
    def test_parse_compact(self):
        compact_sif = """@G graph-001 gemini 2025-12-31T23:59:59Z
N n1 Observation "Log files are linear." 1.0
N n2 Proposition "Thoughts are graphs." 0.95
E n1 contradicts n2 0.9"""
        
        graph = SIFParser.parse(compact_sif)
        
        self.assertEqual(graph.id, "graph-001")
        self.assertEqual(graph.generator, "gemini")
        self.assertEqual(len(graph.nodes), 2)
        self.assertEqual(len(graph.edges), 1)
        
        n1 = next(n for n in graph.nodes if n.id == "n1")
        self.assertEqual(n1.content, "Log files are linear.")
        self.assertEqual(n1.confidence, 1.0)
        
        e1 = graph.edges[0]
        self.assertEqual(e1.source, "n1")
        self.assertEqual(e1.target, "n2")
        self.assertEqual(e1.relation, "contradicts")
        self.assertEqual(e1.weight, 0.9)

    def test_parse_json_still_works(self):
        json_sif = """{
            "@context": "http://sovereign-ai.net/ns/v1",
            "type": "KnowledgeGraph",
            "id": "graph-002",
            "generator": "opus",
            "timestamp": "2025-01-01T00:00:00Z",
            "nodes": [],
            "edges": []
        }"""
        
        graph = SIFParser.parse(json_sif)
        self.assertEqual(graph.id, "graph-002")

if __name__ == '__main__':
    unittest.main()
