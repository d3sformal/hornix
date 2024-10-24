#!/usr/bin/python

import sys
from pathlib import Path
import uuid
import hashlib
import datetime
import subprocess


CHC_SOLVER = './bin/z3'
#CHC_SOLVER = 'golem'
#CHC_SOLVER = 'eldarica'

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


if __name__ == '__main__':
    input_file = sys.argv[1]
    input_cfile = sys.argv[2]

    output = subprocess.run([CHC_SOLVER, input_file], capture_output=True)

    chcoutput = output.stdout.decode('ascii')

    if chcoutput.strip() == 'sat':
        create_witness()
