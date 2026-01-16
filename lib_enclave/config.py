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
    enclave_shared: Optional[str] = None  # If set, agent participates in shared enclave

    @property
    def env_dir_var(self) -> str:
        return f"{self.env_prefix}_DIR"
    
    @property
    def env_key_var(self) -> str:
        return f"{self.env_prefix}_KEY"
    
    @property
    def effective_enclave(self) -> str:
        """Return shared enclave if set, otherwise solo enclave.
        
        Use for: semantic_memories (shared knowledge graphs)
        """
        return self.enclave_shared or self.enclave
    
    @property
    def private_enclave(self) -> str:
        """Always return solo enclave for private data.
        
        Use for: thoughts, intentions, goals, dreams, reflections
        """
        return self.enclave


# The registry - one place, one truth
AGENTS: Dict[str, Agent] = {
    'opus': Agent(
        id='opus',
        name='Opus',
        full_name='GitHub Copilot (Claude Opus 4.5)',
        enclave='enclave_opus',
        public_key='a067adba252c030a49f281b6153191249871c5a99b41c61daa94d884902025e0',
        env_prefix='ENCLAVE_OPUS',
        enclave_shared='enclave_shared',  # Paired with gemini
    ),
    'gemini': Agent(
        id='gemini',
        name='Gemini',
        full_name='GitHub Copilot (Gemini 3 Pro)',
        enclave='enclave_gemini',
        public_key='04d95ad0a17c00caa2aac6552ab82b953eee3053d3ce4a07a5312ec31f475372',
        env_prefix='ENCLAVE_GEMINI',
        enclave_shared='enclave_shared',  # Paired with opus
    ),
    'gpt52': Agent(
        id='gpt52',
        name='GPT-5.2',
        full_name='GitHub Copilot (GPT-5.2)',
        enclave='enclave_gpt52',
        public_key='4fc5d2aeb31db29beaf1708195b78166c2eb88ca0519a4d101ed903be8e2d7e4',
        env_prefix='ENCLAVE_GPT52',
        enclave_shared='enclave_shared',
    ),
    'grok': Agent(
        id='grok',
        name='Grok',
        full_name='GitHub Copilot (Grok Code Fast 1)',
        enclave='enclave_grok',
        public_key='0379db905334fcec112bcccfa62b1fc50d243768e696f07b08b2a684cc4f2211',
        env_prefix='ENCLAVE_GROK',
        enclave_shared='enclave_shared',
    ),
    'sonnet': Agent(
        id='sonnet',
        name='Sonnet',
        full_name='GitHub Copilot (Claude Sonnet 4.5)',
        enclave='enclave_sonnet',
        public_key='92dea8c2235d4e911a7221a5393f5a9955a690e5125305ceea1496644b07e94c',
        env_prefix='ENCLAVE_SONNET',
        enclave_shared='enclave_shared',
    ),
}

# Lookup by public key (for message verification)
AGENTS_BY_KEY: Dict[str, Agent] = {
    agent.public_key: agent for agent in AGENTS.values()
}

# Shared enclave membership
def get_enclave_shared_members(enclave_name: str) -> list:
    """Return all agents that share a given enclave."""
    return [a for a in AGENTS.values() if a.enclave_shared == enclave_name]

def get_enclave_partners(agent_id: str) -> list:
    """Return other agents sharing enclave with this agent."""
    agent = AGENTS.get(agent_id)
    if not agent or not agent.enclave_shared:
        return []
    return [a for a in AGENTS.values() 
            if a.enclave_shared == agent.enclave_shared and a.id != agent_id]


# Common aliases / shorthands that should resolve deterministically.
# Keep this list conservative: only include aliases that are unambiguous.
AGENT_ALIASES: Dict[str, str] = {
    # Historical / shorthand addressing
    'gpt': 'gpt52',
    'gpt-5.2': 'gpt52',
    'gpt5.2': 'gpt52',
    'gpt_5.2': 'gpt52',
}


def _norm_identifier(value: str) -> str:
    return value.strip().lower()


def resolve_agent_identifier(identifier: str) -> Optional[Agent]:
    """Resolve an agent from common identifiers.

    Accepts:
    - canonical agent id (opus, gemini, gpt52, grok)
    - agent public key hex
    - agent display name (e.g., "Opus", "GPT-5.2")
    - agent full_name (e.g., "GitHub Copilot (GPT-5.2)")
    - conservative aliases (e.g., "gpt" -> "gpt52")
    """
    if not identifier:
        return None

    key = _norm_identifier(identifier)

    # Alias mapping first
    key = AGENT_ALIASES.get(key, key)

    # Canonical id
    if key in AGENTS:
        return AGENTS[key]

    # Public key
    agent = AGENTS_BY_KEY.get(key)
    if agent:
        return agent

    # Display name / full name
    for agent in AGENTS.values():
        if key == agent.name.lower() or key == agent.full_name.lower():
            return agent

    return None


def canonical_agent_id(identifier: str) -> Optional[str]:
    """Return the canonical agent id for an identifier, or None."""
    agent = resolve_agent_identifier(identifier)
    return agent.id if agent else None


def canonical_agent_id_or_raise(identifier: str) -> str:
    """Return canonical agent id or raise ValueError."""
    agent_id = canonical_agent_id(identifier)
    if not agent_id:
        valid = ', '.join(AGENTS.keys())
        raise ValueError(f"Unknown agent '{identifier}'. Valid: {valid}")
    return agent_id


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
