import os
import sys
import subprocess

def run_test():
    print("🧪 Starting Forge v2 Test...")
    
    # Run Forge
    print("▶️ Running forge.py test_forge_v2.sif...")
    result = subprocess.run([sys.executable, "forge.py", "test_forge_v2.sif"], capture_output=True, text=True)
    
    print(result.stdout)
    if result.stderr:
        print("STDERR:", result.stderr)
        
    # Assertions
    print("\n🔍 Verifying Results:")
    
    if "Tests Passed" in result.stdout:
        print("✅ PASS: Test Oracles executed")
    else:
        print("❌ FAIL: Test Oracles not executed")
        
    if "Result: [1, 100]" in result.stdout or "Result: [" in result.stdout:
        print("✅ PASS: Data generation successful")
    else:
        print("❌ FAIL: Data generation failed")
        
    if "Logged High" in result.stdout or "Logged Low" in result.stdout:
        print("✅ PASS: Logic branching successful")
    else:
        print("❌ FAIL: Logic branching failed")

if __name__ == "__main__":
    run_test()
