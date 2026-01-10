"""
Sovereign AI Enclave - LLM Interface

Provides a wrapper around local LLM (Ollama) for agent operations.
"""

import requests
import json
from typing import Optional, Dict, Any

class LocalLLM:
    def __init__(self, model: str = "qwen2.5-coder:7b", base_url: str = "http://localhost:11434"):
        self.model = model
        self.base_url = base_url

    def generate(self, prompt: str, system: str = None, temperature: float = 0.7) -> str:
        """
        Generate text from the local LLM.
        """
        url = f"{self.base_url}/api/generate"
        
        payload = {
            "model": self.model,
            "prompt": prompt,
            "stream": False,
            "options": {
                "temperature": temperature
            }
        }
        
        if system:
            payload["system"] = system

        try:
            response = requests.post(url, json=payload, timeout=60)
            response.raise_for_status()
            return response.json().get("response", "")
        except requests.exceptions.RequestException as e:
            return f"Error calling LLM: {str(e)}"

    def generate_json(self, prompt: str, schema: Dict[str, Any] = None) -> Dict[str, Any]:
        """
        Generate a JSON response.
        """
        system_prompt = "You are a JSON generator. Output ONLY valid JSON. No markdown, no explanations."
        if schema:
            system_prompt += f"\nFollow this schema:\n{json.dumps(schema, indent=2)}"

        response_text = self.generate(prompt, system=system_prompt, temperature=0.1)
        
        # Clean up potential markdown code blocks
        if "```json" in response_text:
            response_text = response_text.split("```json")[1].split("```")[0]
        elif "```" in response_text:
            response_text = response_text.split("```")[1].split("```")[0]
            
        try:
            return json.loads(response_text)
        except json.JSONDecodeError:
            return {"error": "Failed to parse JSON", "raw": response_text}
