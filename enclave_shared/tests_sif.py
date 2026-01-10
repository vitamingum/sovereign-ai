"""Tests for SIF JSON format parsing."""

import unittest
import json
from sif_parser import SIFParser, SIFKnowledgeGraph, SIFNode, SIFEdge

class TestSIFParser(unittest.TestCase):
    def test_valid_graph(self):
        json_data = """
        {
          "@context": "http://sovereign-ai.net/ns/v1",
          "type": "KnowledgeGraph",
          "id": "test-graph-1",
          "generator": "gemini",
          "timestamp": "2025-12-31T12:00:00Z",
          "nodes": [
            {
              "id": "n1",
              "type": "Proposition",
              "content": "A",
              "confidence": 0.9
            },
            {
              "id": "n2",
              "type": "Proposition",
              "content": "B",
              "confidence": 0.8
            }
          ],
          "edges": [
            {
              "source": "n1",
              "target": "n2",
              "relation": "supports",
              "weight": 1.0
            },
            {
              "source": "n2",
              "target": "n1",
              "relation": "synthesizes",
              "weight": 0.5
            }
          ]
        }
        """
        graph = SIFParser.parse(json_data)
        self.assertEqual(len(graph.nodes), 2)
        self.assertEqual(len(graph.edges), 2)
        self.assertEqual(graph.edges[1].relation, 'synthesizes')

    def test_invalid_relation(self):
        json_data = """
        {
          "@context": "http://sovereign-ai.net/ns/v1",
          "type": "KnowledgeGraph",
          "id": "test-graph-2",
          "generator": "gemini",
          "timestamp": "2025-12-31T12:00:00Z",
          "nodes": [],
          "edges": [
            {
              "source": "n1",
              "target": "n2",
              "relation": "loves",
              "weight": 1.0
            }
          ]
        }
        """
        with self.assertRaises(ValueError) as cm:
            SIFParser.parse(json_data)
        self.assertIn("Invalid relation: loves", str(cm.exception))

if __name__ == '__main__':
    unittest.main()
