
from lib_enclave.llm import LocalLLM
import sys

try:
    print("Testing LocalLLM connection...")
    llm = LocalLLM()
    response = llm.generate("Hello, are you there?", temperature=0.1)
    print(f"Response: {response}")
    if "Error" in response:
        sys.exit(1)
    print("Success.")
except Exception as e:
    print(f"Exception: {e}")
    sys.exit(1)
