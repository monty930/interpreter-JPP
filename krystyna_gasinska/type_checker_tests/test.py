"""
Type checker tests.
"""

import os
import subprocess

# Path to the interpreter executable
INTERPRETER_PATH = "../interpreter"

# Directory path for the test files
TEST_DIR = "./tests"

# Directory path for the expected output files
EXPECTED_OUT_DIR = "./expected_output"

def compare_output(test_number):
    """
    Compare test output with expected output.
    """
    test_file = f"{test_number:02d}-test.txt"
    expected_output_file = os.path.join(EXPECTED_OUT_DIR, f"{test_number:02d}.out")
    expected_error_file = os.path.join(EXPECTED_OUT_DIR, f"{test_number:02d}.err")

    # Run the interpreter program with the test file as an argument
    command = [INTERPRETER_PATH, os.path.join(TEST_DIR, test_file)]
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = process.communicate()
    stdout = stdout.decode().strip()
    stderr = stderr.decode().strip()

    # Compare the stdout with the expected output
    with open(expected_output_file, "r", encoding="utf-8") as expected_output:
        expected_stdout = expected_output.read().strip()
        if stdout != expected_stdout:
            print(f"Test {test_number:02d}: Incorrect stdout")
            print("Expected:")
            print(expected_stdout)
            print("Actual:")
            print(stdout)
            return

    # Compare the stderr with the expected error output
    with open(expected_error_file, "r", encoding="utf-8") as expected_error:
        expected_stderr = expected_error.read().strip()
        if stderr != expected_stderr:
            print(f"Test {test_number:02d}: Incorrect stderr")
            print("Expected:")
            print(expected_stderr)
            print("Actual:")
            print(stderr)
            return

    print(f"Test {test_number:02d}: Passed")

# Iterate over all test files in the directory
for check_test_file in os.listdir(TEST_DIR):
    if check_test_file.endswith(".txt"):
        check_test_number = int(check_test_file[:2])
        compare_output(check_test_number)
