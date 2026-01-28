import os
import subprocess
import tomllib
import re
import sys
from unittest import result


def load_tests(config_path):
    with open(config_path, "rb") as f:
        data = tomllib.load(f)
    return data["tests"]

def find_signature_address(binary_path):
    """Finds the address of the 'signature' symbol."""
    cmd = f"objdump -t {binary_path} | grep 'signature'"
    result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    if result.returncode != 0:
        return None

    # Example output: 0000000000004030 g     O .bss	0000000000000008              signature
    match = re.search(r"([0-9a-f]+) .*\bsignature\b", result.stdout)
    if match:
        return int(match.group(1), 16)
    return None

def run_test(test):
    test_name = test["test_name"]
    binary_path = f"./build/test/{test_name}/{test_name}.out"

    if not os.path.exists(binary_path):
        print(f"SKIP: {test_name}(Binary not found)")
        return False

    match = re.search(r"([0-9a-f]+) .*\bsignature\b", result.stdout)
    if match:
        return int(match.goup(1),16)
    return None

def find_fault_injection_point(binary_path, signature_addr):
    """
    Finds a suitable instruction to skip.
    Looking for:
      add $0x..., %reg
      mov %reg, signature_addr(%rip)
    """
    cmd = f"objdump -d {binary_path} | grep -A 20 '<main>:'" # heuristic: look in main first
    # Using a broader dump
    cmd = f"objdump -d {binary_path}"
    result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    if result.returncode != 0:
        return None, None

    lines = result.stdout.splitlines()
    for i, line in enumerate(lines):
        if "<signature>" in line and "mov" in line:
            pass

    return None,None

def analyze_with_gdb(binary_path):
    gdb_cmd = f"gdb --batch -ex 'file {binary_path}' -ex 'disassemble main'"
    result = subprocess.run(gdb_cmd, shell=True, capture_output=True, text=True)
    lines = result.stdout.splitlines()

    for i in range(len(lines)):
        line = lines[i]
        # Match address and offset: 0x... <+36>: add ...
        # Regex: start, addr, <offset>, mnemonic, operands
        m = re.search(r"^0x[0-9a-f]+\s+<(\+\d+)>:\s+add\s+\$(0x[0-9a-f]+),", line.strip())
        if m:
            offset_str = m.group(1) # "+36"

            # Calculate length by looking at next instruction
            if i + 1 < len(lines):
                next_line = lines[i+1]
                m_next_addr = re.search(r"^(0x[0-9a-f]+)", next_line.strip())
                m_curr_addr = re.search(r"^(0x[0-9a-f]+)", line.strip())

                if m_next_addr and m_curr_addr:
                    length = int(m_next_addr.group(1), 16) - int(m_curr_addr.group(1), 16)
                    return offset_str, length
    return None, None
def run_test(test):
    test_name = test["test_name"]
    binary_path = f"./build/test/{test_name}/{test_name}.out"

    if not os.path.exists(binary_path):
        print(f"SKIP: {test_name} (Binary not found)")
        return False

    offset_str, length = analyze_with_gdb(binary_path)

    if not offset_str:
        print(f"SKIP: {test_name} (No suitable injection point found)")
        return False

    # Create GDB script
    gdb_script = f"""file {binary_path}
break *main{offset_str}
run
set $pc = $pc + {length}
continue
quit
"""
    script_path = f"verify_{test_name}.gdb"
    with open(script_path, "w") as f:
        f.write(gdb_script)

    try:
        result = subprocess.run(f"gdb --batch -x {script_path}", shell=True, capture_output=True, text=True, timeout=5)
    except subprocess.TimeoutExpired:
        print(f"FAIL: {test_name} (Timed out)")
        if os.path.exists(script_path):
            os.remove(script_path)
        return False

    output = result.stdout + result.stderr

    # Check for text or exit code or SegFault (which implies protection triggered in some cases?)
    # But usually we want explicit detection.
    # If the handler is missing, maybe it segfaults.
    # Let's count SIGSEGV as a "partial pass" or just print it.

    passed = ("Signature Mismatch Detected" in output) or ("exited with code 02" in output)

    if passed:
        print(f"PASS: {test_name}")
    else:
        print(f"FAIL: {test_name}")
        print("Output snippet:", output[:200].replace('\n', ' '))

    if os.path.exists(script_path):
        os.remove(script_path)
    return passed

if __name__ == "__main__":
    tests = load_tests("../testing/config/racfed+eddi.toml")
    passed_count = 0
    total = 0
    for test in tests:
        if run_test(test):
            passed_count += 1
        total += 1

    print(f"Summary: {passed_count}/{total} passed fault injection.")
