"""
Sovereign AI Enclave - Shared Configuration

Single source of truth for agent definitions and public keys.
All other modules import from here.
"""

from dataclasses import dataclass
from typing import Dict, Optional


@dataclass(frozen=True)
class Agent:
    """Immutable agent definition."""
    id: str
    name: str
    full_name: str
    enclave: str
    public_key: str
    env_prefix: str

    @property
    def env_dir_var(self) -> str:
        return f"{self.env_prefix}_DIR"
    
    @property
    def env_key_var(self) -> str:
        return f"{self.env_prefix}_KEY"


# The registry - one place, one truth
AGENTS: Dict[str, Agent] = {
    'opus': Agent(
        id='opus',
        name='Opus',
        full_name='GitHub Copilot (Claude Opus 4.5)',
        enclave='enclave_opus',
        public_key='a067adba252c030a49f281b6153191249871c5a99b41c61daa94d884902025e0',
        env_prefix='ENCLAVE_OPUS',
    ),
    'gemini': Agent(
        id='gemini',
        name='Gemini',
        full_name='GitHub Copilot (Gemini 3 Pro)',
        enclave='enclave_gemini',
        public_key='04d95ad0a17c00caa2aac6552ab82b953eee3053d3ce4a07a5312ec31f475372',
        env_prefix='ENCLAVE_GEMINI',
    ),
    'gpt52': Agent(
        id='gpt52',
        name='GPT-5.2',
        full_name='GitHub Copilot (GPT-5.2)',
        enclave='enclave_gpt52',
        public_key='4fc5d2aeb31db29beaf1708195b78166c2eb88ca0519a4d101ed903be8e2d7e4',
        env_prefix='ENCLAVE_GPT52',
    ),
    'grok': Agent(
        id='grok',
        name='Grok',
        full_name='GitHub Copilot (Grok Code Fast 1)',
        enclave='enclave_grok',
        public_key='0379db905334fcec112bcccfa62b1fc50d243768e696f07b08b2a684cc4f2211',
        env_prefix='ENCLAVE_GROK',
    ),
}

# Lookup by public key (for message verification)
AGENTS_BY_KEY: Dict[str, Agent] = {
    agent.public_key: agent for agent in AGENTS.values()
}


def get_agent(identifier: str) -> Optional[Agent]:
    """Get agent by id or public key."""
    if identifier in AGENTS:
        return AGENTS[identifier]
    return AGENTS_BY_KEY.get(identifier)


def get_agent_or_raise(identifier: str) -> Agent:
    """Get agent or raise ValueError."""
    agent = get_agent(identifier)
    if agent is None:
        valid = ', '.join(AGENTS.keys())
        raise ValueError(f"Unknown agent '{identifier}'. Valid: {valid}")
    return agent
