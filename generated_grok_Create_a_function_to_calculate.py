```python
def calculate_semantic_similarity(node1, node2):
    """
    Calculate semantic similarity between two SIF nodes.

    Parameters:
    - node1 (dict): The first SIF node represented as a dictionary.
    - node2 (dict): The second SIF node represented as a dictionary.

    Returns:
    float: The semantic similarity score between the two nodes.

    Raises:
    ValueError: If either node is not a valid dictionary or does not contain required keys.
    """

    if not isinstance(node1, dict) or not isinstance(node2, dict):
        raise ValueError("Both inputs must be dictionaries.")

    required_keys = {'id', 'embedding'}
    if not (required_keys.issubset(set(node1.keys())) and required_keys.issubset(set(node2.keys()))):
        missing_keys = required_keys - set(node1.keys()) or required_keys - set(node2.keys())
        raise ValueError(f"Missing keys: {missing_keys}")

    embedding1 = node1['embedding']
    embedding2 = node2['embedding']

    if len(embedding1) != len(embedding2):
        raise ValueError("Embeddings must be of the same length.")

    # Example similarity calculation (replace with actual implementation)
    dot_product = sum(a * b for a, b in zip(embedding1, embedding2))
    magnitude1 = sum(x ** 2 for x in embedding1) ** 0.5
    magnitude2 = sum(x ** 2 for x in embedding2) ** 0.5

    similarity_score = dot_product / (magnitude1 * magnitude2)

    return similarity_score
```