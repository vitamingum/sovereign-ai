
import sys
import os
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from cryptography.hazmat.primitives import hashes

def derive_key(passphrase: str, salt: bytes) -> bytes:
    kdf = PBKDF2HMAC(
        algorithm=hashes.SHA256(),
        length=32,
        salt=salt,
        iterations=480000,
    )
    return kdf.derive(passphrase.encode())

def try_decrypt(passphrase, nonce_hex, content_hex):
    salt = b"sovereign_memory_salt_v1"
    try:
        key = derive_key(passphrase, salt)
        aesgcm = AESGCM(key)
        nonce = bytes.fromhex(nonce_hex)
        content = bytes.fromhex(content_hex)
        decrypted = aesgcm.decrypt(nonce, content, None)
        return decrypted.decode('utf-8')
    except Exception as e:
        return None

nonce = "21bef4c83cb41aec9dd5e840"
content = "f3ef5b44098a14e9526c8eea46fe035bad2586f917e8e4ca58288878c46beed1f480fd7b8a15886c992221581696d3d4d31c4b2b81210bbddef82b50c15601327c06154a7555f547bb84ea1d4cb7c74eb42d8c036b8bf45904a4216ff53c9d4290dc9335ab956cf50efbc8807f94ac80e6"

candidates = [
    "your-passphrase",
    "test-passphrase-12345",
    "sovereign-enclave-memory-identity",
    "correct-horse-battery-staple",
    "example-passphrase",
    "passphrase",
    "enclave",
    "gemini",
    "sovereign",
    "identity"
]

print("Attempting decryption...")
for p in candidates:
    result = try_decrypt(p, nonce, content)
    if result:
        print(f"SUCCESS! Passphrase: '{p}'")
        print(f"Content: {result}")
        break
else:
    print("Failed to decrypt with any candidate.")
