"""
Council API Configuration
Reads API keys from .env file
"""
import os
from pathlib import Path
from dataclasses import dataclass


@dataclass
class APIConfig:
    gemini_key: str | None
    gpt_key: str | None
    grok_key: str | None


def load_env():
    """Load .env file from council directory."""
    env_path = Path(__file__).parent / ".env"
    if env_path.exists():
        with open(env_path, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith("#") and "=" in line:
                    key, value = line.split("=", 1)
                    os.environ[key.strip()] = value.strip()


def load_config() -> APIConfig:
    """Load API keys from .env file."""
    load_env()
    return APIConfig(
        gemini_key=os.environ.get("GOOGLE_API_KEY"),
        gpt_key=os.environ.get("OPENAI_API_KEY"),
        grok_key=os.environ.get("XAI_API_KEY"),
    )


def require_key(key: str | None, name: str) -> str:
    """Raise if key is missing."""
    if not key:
        raise ValueError(f"{name} not set. Add to council/.env")
    return key
