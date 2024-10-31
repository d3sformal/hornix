#!/usr/bin/env python3

import sys
from pathlib import Path
import uuid
import hashlib
import datetime
import subprocess


OUTPUT_TEMPLATE = '''\
- entry_type: "invariant_set"
  metadata:
    format_version: "2.0"
    uuid: "{UUID}"
    creation_time: "{CREATION_TIME}+01:00"
    producer:
      name: "Hornix"
      version: "0.1.0"
      configuration: "svcomp25"
    task:
      input_files:
      - "./{INPUT_FILE}"
      input_file_hashes:
        "./{INPUT_FILE}": "{SHA256SUM}"
      specification: "G ! call(reach_error())"
      data_model: "ILP32"
      language: "C"
  content: []
'''


def create_witness():
    global uuid

    data = list()
    # data['entry_type'] = ''
    # data['invariant'] = ''
    # data['content'] = ''

    output_file = Path(input_file).stem + '.witness.yml'
    uuid = uuid.uuid4()
    with open(input_cfile, 'rb') as f:
        sha256 = hashlib.sha256(f.read()).hexdigest()


    with open(output_file, 'wt') as f:
        f.write(OUTPUT_TEMPLATE.format(INPUT_FILE=input_cfile, UUID=uuid, SHA256SUM=sha256, CREATION_TIME=str(datetime.datetime.now().isoformat(timespec='seconds'))))

def run_z3(input_file, timeout = 900):
    # timeout in seconds, default 15 minutes
    return subprocess.run(['z3', f"-T:{timeout}", input_file], capture_output=True, text=True)

def run_golem(input_file, engine = 'spacer', timeout = 900):
    # timeout in seconds, default 15 minutes
    try:
        #return subprocess.run(['golem', "--engine", engine, "--print-witness", "-i", input_file], capture_output=True, text=True, timeout=timeout)
        return subprocess.run(['golem', "--engine", engine, "-i", input_file], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired as e:
        return subprocess.CompletedProcess(
            args=e.cmd,                  # Original command
            returncode=None,             # No return code since it timed out
            stdout=e.stdout,             # Partial output before timeout
            stderr=e.stderr              # Partial error output, if any
        )


if __name__ == '__main__':
    input_file = sys.argv[1]
    input_cfile = sys.argv[2]

    process_result = run_z3(input_file)
    #process_result = run_golem(input_file, engine = 'spacer', timeout = 10)
    if process_result.returncode == None:
        print('timeout')
        exit(1)
    if process_result.returncode != 0:
        print('error')
        exit(1)
    output = process_result.stdout

    print(output, end='')
    if output.strip() == 'sat':
        create_witness()
