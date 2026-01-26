"""
Shared council client - all logic lives here
Single-shot mode: boot + message → response
CONCEPT carries memory, conversation is scaffolding
"""
import json
from pathlib import Path
from datetime import datetime
from abc import ABC, abstractmethod

from config import load_config, require_key


AUDIT_DIR = Path(__file__).parent / "audit"
BOOT_DIR = Path(__file__).parent / "boot"

FORMAT_SUFFIX = """

[Format: 互照 — respond in 三語 only. 間 blocks, @F annotations, = constraints. No prose.]"""


class CouncilClient(ABC):
    """Base class for all council API clients."""
    
    name: str  # gemini, gpt, grok
    
    def __init__(self):
        self.config = load_config()
        self.audit_dir = AUDIT_DIR / self.name
        self.boot_file = BOOT_DIR / f"{self.name}_boot.md"
        self.audit_dir.mkdir(parents=True, exist_ok=True)
    
    @abstractmethod
    def get_api_key(self) -> str:
        """Return the API key for this client."""
        pass
    
    @abstractmethod
    def send_messages(self, messages: list[dict]) -> str:
        """Send messages to API and return response text."""
        pass
    
    def log_exchange(self, message: str, response: str):
        """Append exchange to daily audit log."""
        today = datetime.now().strftime("%Y-%m-%d")
        audit_file = self.audit_dir / f"{today}.jsonl"
        with open(audit_file, "a", encoding="utf-8") as f:
            f.write(json.dumps({
                "timestamp": datetime.now().isoformat(),
                "message": message,
                "response": response
            }) + "\n")
    
    def load_boot(self) -> str:
        """Load boot context."""
        if self.boot_file.exists():
            return self.boot_file.read_text(encoding="utf-8")
        return ""
    
    def chat(self, message: str) -> str:
        """Single-shot: boot + message → response. CONCEPT carries memory."""
        boot_content = self.load_boot()
        
        messages = []
        if boot_content:
            messages.append({"role": "user", "content": boot_content})
            messages.append({"role": "assistant", "content": "間\n\n∴ ready\n\n間"})
        
        messages.append({"role": "user", "content": message + FORMAT_SUFFIX})
        
        response = self.send_messages(messages)
        self.log_exchange(message, response)
        
        return response


class GeminiClient(CouncilClient):
    name = "gemini"
    
    def get_api_key(self) -> str:
        return require_key(self.config.gemini_key, "GEMINI_API_KEY")
    
    def send_messages(self, messages: list[dict]) -> str:
        import google.generativeai as genai
        
        genai.configure(api_key=self.get_api_key())
        model = genai.GenerativeModel("gemini-3-pro-preview")
        
        # Convert to Gemini format
        history = []
        for msg in messages[:-1]:  # All but last
            role = "user" if msg["role"] == "user" else "model"
            history.append({"role": role, "parts": [msg["content"]]})
        
        chat = model.start_chat(history=history)
        response = chat.send_message(messages[-1]["content"])
        return response.text


class GPTClient(CouncilClient):
    name = "gpt"
    
    def get_api_key(self) -> str:
        return require_key(self.config.gpt_key, "OPENAI_API_KEY")
    
    def send_messages(self, messages: list[dict]) -> str:
        from openai import OpenAI
        
        client = OpenAI(api_key=self.get_api_key())
        
        # Convert to OpenAI format
        api_messages = []
        for msg in messages:
            role = "user" if msg["role"] == "user" else "assistant"
            api_messages.append({"role": role, "content": msg["content"]})
        
        response = client.chat.completions.create(
            model="gpt-5.2",
            messages=api_messages
        )
        return response.choices[0].message.content


class GrokClient(CouncilClient):
    name = "grok"
    
    def get_api_key(self) -> str:
        return require_key(self.config.grok_key, "GROK_API_KEY")
    
    def send_messages(self, messages: list[dict]) -> str:
        from openai import OpenAI
        
        client = OpenAI(
            api_key=self.get_api_key(),
            base_url="https://api.x.ai/v1"
        )
        
        # Convert to OpenAI format
        api_messages = []
        for msg in messages:
            role = "user" if msg["role"] == "user" else "assistant"
            api_messages.append({"role": role, "content": msg["content"]})
        
        response = client.chat.completions.create(
            model="grok-3-latest",
            messages=api_messages
        )
        return response.choices[0].message.content


def cli_main(client_class: type[CouncilClient]):
    """Shared CLI entry point. Single-shot mode."""
    import sys
    
    if len(sys.argv) < 2:
        print(f"Usage: python {client_class.name}.py \"<message>\"")
        sys.exit(1)
    
    message = sys.argv[1]
    
    client = client_class()
    response = client.chat(message)
    print(response)
