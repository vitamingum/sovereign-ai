"""
Sovereign AI Enclave - Graph Memory Module

Extends SemanticMemory with explicit connections between memories.
Implements spreading activation for robust retrieval.

Based on research: connected memories are 55% more robust to perturbation.
"""

import json
import numpy as np
from datetime import datetime, timezone
from pathlib import Path
from typing import List, Dict, Optional, Tuple
from collections import defaultdict

from .semantic_memory import SemanticMemory


class GraphMemory(SemanticMemory):
    """
    Semantic memory with graph structure for robust retrieval.
    
    Extends base semantic memory with:
    - Explicit connections between memories (supports, contradicts, elaborates, etc.)
    - Spreading activation for noise-robust retrieval
    - Connection strength tracking
    - Consolidation counts
    """
    
    CONNECTION_TYPES = ['supports', 'contradicts', 'elaborates', 'precedes', 'related']
    
    def __init__(self, enclave_path: str = None):
        super().__init__(enclave_path)
        self._graph = None  # Lazy-loaded connection graph
        self._access_log = defaultdict(int)  # Track access frequency
        
    def _load_graph(self) -> Dict[str, List[Dict]]:
        """Load connection graph from storage."""
        if self._graph is not None:
            return self._graph
            
        graph_file = self.private_path / "memory_graph.json"
        if graph_file.exists():
            with open(graph_file, "r", encoding="utf-8") as f:
                self._graph = json.load(f)
        else:
            self._graph = {}
        return self._graph
    
    def _save_graph(self):
        """Persist connection graph."""
        self.private_path.mkdir(parents=True, exist_ok=True)
        graph_file = self.private_path / "memory_graph.json"
        with open(graph_file, "w", encoding="utf-8") as f:
            json.dump(self._graph, f, indent=2)
    
    def connect(self, source_id: str, target_id: str, 
                connection_type: str = 'related', 
                strength: float = 0.5,
                bidirectional: bool = True) -> bool:
        """
        Create connection between two memories.
        
        Args:
            source_id: Source memory ID
            target_id: Target memory ID
            connection_type: One of CONNECTION_TYPES
            strength: Connection strength (0-1)
            bidirectional: If True, create reverse connection too
            
        Returns:
            True if connection created successfully
        """
        if connection_type not in self.CONNECTION_TYPES:
            raise ValueError(f"Unknown connection type: {connection_type}")
        
        graph = self._load_graph()
        
        # Add forward connection
        if source_id not in graph:
            graph[source_id] = []
        
        # Update existing or add new
        existing = next((c for c in graph[source_id] if c['target'] == target_id), None)
        if existing:
            existing['strength'] = strength
            existing['type'] = connection_type
        else:
            graph[source_id].append({
                'target': target_id,
                'type': connection_type,
                'strength': strength,
                'created': datetime.now(timezone.utc).isoformat()
            })
        
        # Add reverse connection if bidirectional
        if bidirectional:
            if target_id not in graph:
                graph[target_id] = []
            
            reverse_type = connection_type
            if connection_type == 'precedes':
                reverse_type = 'follows'  # Semantic reverse
            
            existing_rev = next((c for c in graph[target_id] if c['target'] == source_id), None)
            if existing_rev:
                existing_rev['strength'] = strength
                existing_rev['type'] = reverse_type
            else:
                graph[target_id].append({
                    'target': source_id,
                    'type': reverse_type,
                    'strength': strength,
                    'created': datetime.now(timezone.utc).isoformat()
                })
        
        self._save_graph()
        return True
    
    def get_connections(self, memory_id: str) -> List[Dict]:
        """Get all connections for a memory."""
        graph = self._load_graph()
        return graph.get(memory_id, [])
    
    def recall_with_spreading(self, query: str, top_k: int = 5, 
                              threshold: float = 0.3,
                              spread_depth: int = 2,
                              spread_decay: float = 0.5) -> List[dict]:
        """
        Find memories using spreading activation through connection graph.
        
        More robust than simple similarity - connected memories boost each other.
        
        Args:
            query: Natural language query
            top_k: Maximum results
            threshold: Minimum final activation score
            spread_depth: How many hops to spread activation
            spread_decay: Decay factor per hop (0-1)
            
        Returns:
            List of memories with activation scores
        """
        if not self._encryption_key:
            raise RuntimeError("Memory not unlocked")
        
        # Get initial similarity scores
        base_results = self.recall_similar(query, top_k=50, threshold=0.0)
        
        if not base_results:
            return []
        
        # Initialize activation from similarity
        activation = {r['id']: r['similarity'] for r in base_results}
        
        # Spreading activation
        graph = self._load_graph()
        
        for depth in range(spread_depth):
            new_activation = activation.copy()
            decay = spread_decay ** (depth + 1)
            
            for mem_id, score in activation.items():
                if score <= 0:
                    continue
                    
                connections = graph.get(mem_id, [])
                for conn in connections:
                    target = conn['target']
                    spread_amount = score * conn['strength'] * decay
                    
                    if target in new_activation:
                        new_activation[target] += spread_amount
                    else:
                        new_activation[target] = spread_amount
            
            activation = new_activation
        
        # Filter by threshold and get content
        results = []
        all_memories = {m['id']: m for m in self.recall_all()}
        
        for mem_id, score in activation.items():
            if score >= threshold and mem_id in all_memories:
                mem = all_memories[mem_id]
                results.append({
                    **mem,
                    'activation': score,
                    'connections': graph.get(mem_id, [])
                })
                # Track access
                self._access_log[mem_id] += 1
        
        results.sort(key=lambda x: x['activation'], reverse=True)
        return results[:top_k]
    
    def auto_connect(self, memory_id: str, threshold: float = 0.6) -> int:
        """
        Automatically connect a memory to similar memories.
        
        Args:
            memory_id: Memory to connect
            threshold: Minimum similarity for auto-connection
            
        Returns:
            Number of connections created
        """
        all_memories = self.recall_all()
        target_mem = next((m for m in all_memories if m['id'] == memory_id), None)
        
        if not target_mem:
            return 0
        
        # Find similar memories
        similar = self.recall_similar(target_mem['content'], top_k=10, threshold=threshold)
        
        connections_made = 0
        for mem in similar:
            if mem['id'] != memory_id:
                self.connect(memory_id, mem['id'], 
                           connection_type='related',
                           strength=mem['similarity'])
                connections_made += 1
        
        return connections_made
    
    def remember_connected(self, thought: str, tags: List[str] = None,
                          auto_connect_threshold: float = 0.6) -> dict:
        """
        Store a memory and automatically connect it to related memories.
        
        Args:
            thought: Content to store
            tags: Optional tags
            auto_connect_threshold: Min similarity for auto-connections
            
        Returns:
            Dict with memory ID and connection count
        """
        # Store the memory
        result = self.remember(thought, tags)
        
        if not result.get('stored'):
            return result
        
        # Auto-connect
        connections = self.auto_connect(result['id'], auto_connect_threshold)
        
        return {
            **result,
            'connections_created': connections
        }
    
    def get_memory_stats(self) -> Dict:
        """Get statistics about the memory graph."""
        graph = self._load_graph()
        all_memories = self.recall_all()
        
        total_connections = sum(len(conns) for conns in graph.values())
        memories_with_connections = len([m for m in all_memories if m['id'] in graph])
        isolated = len(all_memories) - memories_with_connections
        
        # Find clusters (simple connected components)
        visited = set()
        clusters = []
        
        def dfs(node, cluster):
            if node in visited:
                return
            visited.add(node)
            cluster.add(node)
            for conn in graph.get(node, []):
                dfs(conn['target'], cluster)
        
        for mem in all_memories:
            if mem['id'] not in visited:
                cluster = set()
                dfs(mem['id'], cluster)
                if len(cluster) > 1:
                    clusters.append(cluster)
        
        return {
            'total_memories': len(all_memories),
            'total_connections': total_connections,
            'avg_connections': total_connections / max(len(all_memories), 1),
            'isolated_memories': isolated,
            'cluster_count': len(clusters),
            'largest_cluster': max(len(c) for c in clusters) if clusters else 0,
            'access_counts': dict(self._access_log)
        }
    
    def find_isolated(self, min_connections: int = 1) -> List[str]:
        """Find memories with fewer than min_connections."""
        graph = self._load_graph()
        all_memories = self.recall_all()
        
        isolated = []
        for mem in all_memories:
            conn_count = len(graph.get(mem['id'], []))
            if conn_count < min_connections:
                isolated.append(mem['id'])
        
        return isolated


# Ensure 'follows' is recognized as valid reverse type
GraphMemory.CONNECTION_TYPES.append('follows')


if __name__ == "__main__":
    print("Sovereign AI - Graph Memory Module")
    print("Extends semantic memory with connection graph for robust retrieval")
