"""
Type checker tests.
"""

import os
import subprocess

# Path to the interpreter executable
INTERPRETER_PATH = "../interpreter"

PATH_FOR_INTERPRETER = "./type_checker_tests/tests/"

# Directory path for the test files
TEST_DIR = "./tests/"
absolute_path = os.path.dirname(__file__)
TEST_DIR = os.path.join(absolute_path, TEST_DIR)

# Directory path for the expected output files
EXPECTED_OUT_DIR = "./expected_output"
EXPECTED_OUT_DIR = os.path.join(absolute_path, EXPECTED_OUT_DIR)

FILE_LIST = sorted(os.listdir(TEST_DIR))

for file in FILE_LIST:
    file_path = os.path.join(TEST_DIR, file)
    file_path_arg_int = os.path.join(PATH_FOR_INTERPRETER, file)
    output_path = os.path.join(EXPECTED_OUT_DIR, file[0:2] + ".out")
    error_output_path = os.path.join(EXPECTED_OUT_DIR, file[0:2] + ".err")

    process = subprocess.Popen(["./interpreter", file_path_arg_int], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = process.communicate()

    # Read the expected output
    with open(output_path, 'r', encoding='utf-8') as f:
        expected_output = f.read()

    # Read the expected error output
    with open(error_output_path, 'r', encoding='utf-8') as f:
        expected_err_output = f.read()

    # Compare the output with the expected output
    if stdout.decode().strip() != expected_output.strip():
        print(f"Output for {file_path_arg_int} is incorrect.")
        print("Expected output:")
        print(expected_output)
        print("Actual output:")
        print(stdout.decode())
        break

    # Compare the error output with the expected error output
    if stderr.decode().strip() != expected_err_output.strip():
        print(f"Error output for {file_path_arg_int} is incorrect.")
        print("Expected error output:")
        print(expected_err_output)
        print("Actual error output:")
        print(stderr.decode())
        break

else:
    print("All 'type_checker' outputs are correct. Number of tests: " + str(len(FILE_LIST)))
