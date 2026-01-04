import os
import sys
import subprocess
import time

def run_test():
    print("🧪 Starting Forge Prototype Test...")
    
    # Cleanup previous run
    for f in ["app.log", "logs.zip", "status.txt"]:
        if os.path.exists(f):
            os.remove(f)
            
    # Run Forge
    print("▶️ Running forge.py test_forge.sif...")
    result = subprocess.run([sys.executable, "forge.py", "test_forge.sif"], capture_output=True, text=True)
    
    print(result.stdout)
    if result.stderr:
        print("STDERR:", result.stderr)
        
    # Assertions
    print("\n🔍 Verifying Results:")
    
    # 1. app.log should be deleted (because we zipped it)
    if not os.path.exists("app.log"):
        print("✅ PASS: app.log was deleted")
    else:
        print("❌ FAIL: app.log still exists")
        
    # 2. logs.zip should exist
    if os.path.exists("logs.zip"):
        print("✅ PASS: logs.zip created")
    else:
        print("❌ FAIL: logs.zip missing")
        
    # 3. status.txt should exist and contain "Done"
    if os.path.exists("status.txt"):
        with open("status.txt", "r") as f:
            content = f.read()
        if content == "Done":
            print("✅ PASS: status.txt contains 'Done'")
        else:
            print(f"❌ FAIL: status.txt contains '{content}'")
    else:
        print("❌ FAIL: status.txt missing")

if __name__ == "__main__":
    run_test()
