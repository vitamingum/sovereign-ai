#!/usr/bin/env python3
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from enclave.crypto import SovereignIdentity

# For grok
enclave_path = "enclave_grok"
passphrase = "copilot-opus-4.5-sovereign-2025"

print(f"Generating identity for {enclave_path}")
identity = SovereignIdentity(enclave_path)
result = identity.generate_identity(passphrase)
print("Identity generated:", result)