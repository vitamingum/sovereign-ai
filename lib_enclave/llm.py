"""
Sovereign AI Enclave - LLM Interface

Provides a wrapper around local LLM (Ollama) for agent operations.
"""

import requests
import json
from typing import Optional, Dict, Any

class LocalLLM:
    def __init__(self, model: str = "deepseek-r1:14b", base_url: str = "http://localhost:11434"):
        self.model = model
        self.base_url = base_url

    def generate(self, prompt: str, system: str = None, temperature: float = 0.7, quiet: bool = False) -> str:
        """
        Generate text from the local LLM.
        """
        url = f"{self.base_url}/api/generate"
        
        payload = {
            "model": self.model,
            "prompt": prompt,
            "stream": True,
            "options": {
                "temperature": temperature
            }
        }
        
        if system:
            payload["system"] = system

        try:
            # Bypass proxies for localhost
            session = requests.Session()
            session.trust_env = False
            
            response = session.post(url, json=payload, stream=True, timeout=300)
            response.raise_for_status()
            
            full_response = ""
            if not quiet:
                print("      thinking", end="", flush=True)
            dot_count = 0
            for line in response.iter_lines():
                if line:
                    decoded = json.loads(line.decode('utf-8'))
                    if "response" in decoded:
                        content = decoded["response"]
                        full_response += content
                        dot_count += 1
                        if not quiet and dot_count % 50 == 0:
                            print(".", end="", flush=True)
                    if decoded.get("done", False):
                        break
            if not quiet:
                print()
            return full_response

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
