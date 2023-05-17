import os
import subprocess

# Directory for interpreter
dir_for_interpreter = "./bad/"

input_dir = "../bad/"
output_dir = "./expected_output/bad/"

absolute_path = os.path.dirname(__file__)
input_dir = os.path.join(absolute_path, input_dir)
output_dir = os.path.join(absolute_path, output_dir)

# Get a list of all files in the bad directory
file_list = sorted(os.listdir(input_dir))

for file_name in file_list:
    # Construct the file paths
    file_path = os.path.join(input_dir, file_name)
    file_path_arg_int = os.path.join(dir_for_interpreter, file_name)
    
    output_path = os.path.join(output_dir, file_name[3:5] + ".out")

    output_err_path = os.path.join(output_dir, file_name[3:5] + ".err")

    # Run the interpreter with the file path as an argument
    process = subprocess.Popen(["./interpreter", file_path_arg_int], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = process.communicate()

    # Read the expected output
    with open(output_path, 'r') as f:
        expected_output = f.read()

    # Read the expected error output
    with open(output_err_path, 'r') as f:
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
    print("All 'bad' outputs are correct.")

# Directory for interpreter
dir_for_interpreter = "./good/"

input_dir = "../good/"
output_dir = "./expected_output/good/"

absolute_path = os.path.dirname(__file__)
input_dir = os.path.join(absolute_path, input_dir)
output_dir = os.path.join(absolute_path, output_dir)

# Get a list of all files in the bad directory
file_list = sorted(os.listdir(input_dir))

for file_name in file_list:
    # Construct the file paths
    file_path = os.path.join(input_dir, file_name)
    file_path_arg_int = os.path.join(dir_for_interpreter, file_name)
    
    output_path = os.path.join(output_dir, file_name[0:2] + ".out")

    # Run the interpreter with the file path as an argument
    process = subprocess.Popen(["./interpreter", file_path_arg_int], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = process.communicate()

    # Read the expected output
    with open(output_path, 'r') as f:
        expected_output = f.read()

    # Compare the output with the expected output
    if stdout.decode().strip() != expected_output.strip():
        print(f"Output for {file_path_arg_int} is incorrect.")
        print("Expected output:")
        print(expected_output)
        print("Actual output:")
        print(stdout.decode())
        break

    # Compare the error output with the expected error output
    if stderr.decode().strip() != "":
        print(f"Error output for {file_path_arg_int} is incorrect.")
        print("Expected error output:")
        print("Actual error output:")
        print(stderr.decode())
        break

else:
    print("All 'good' outputs are correct.")