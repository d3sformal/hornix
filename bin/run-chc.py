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


WITNESS_TEMPLATE_V1 = '''\
<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<graphml xmlns="http://graphml.graphdrawing.org/xmlns" xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance">
 <key attr.name="originFileName" attr.type="string" for="edge" id="originfile">
  <default>{INPUT_FILE}</default>
 </key>
 <key attr.name="invariant" attr.type="string" for="node" id="invariant"/>
 <key attr.name="invariant.scope" attr.type="string" for="node" id="invariant.scope"/>
 <key attr.name="namedValue" attr.type="string" for="node" id="named"/>
 <key attr.name="nodeType" attr.type="string" for="node" id="nodetype">
  <default>path</default>
 </key>
 <key attr.name="isFrontierNode" attr.type="boolean" for="node" id="frontier">
  <default>false</default>
 </key>
 <key attr.name="isViolationNode" attr.type="boolean" for="node" id="violation">
  <default>false</default>
 </key>
 <key attr.name="isEntryNode" attr.type="boolean" for="node" id="entry">
  <default>false</default>
 </key>
 <key attr.name="isSinkNode" attr.type="boolean" for="node" id="sink">
  <default>false</default>
 </key>
 <key attr.name="enterLoopHead" attr.type="boolean" for="edge" id="enterLoopHead">
  <default>false</default>
 </key>
 <key attr.name="violatedProperty" attr.type="string" for="node" id="violatedProperty"/>
 <key attr.name="threadId" attr.type="string" for="edge" id="threadId"/>
 <key attr.name="sourcecodeLanguage" attr.type="string" for="graph" id="sourcecodelang"/>
 <key attr.name="programFile" attr.type="string" for="graph" id="programfile"/>
 <key attr.name="programHash" attr.type="string" for="graph" id="programhash"/>
 <key attr.name="specification" attr.type="string" for="graph" id="specification"/>
 <key attr.name="architecture" attr.type="string" for="graph" id="architecture"/>
 <key attr.name="producer" attr.type="string" for="graph" id="producer"/>
 <key attr.name="sourcecode" attr.type="string" for="edge" id="sourcecode"/>
 <key attr.name="startline" attr.type="int" for="edge" id="startline"/>
 <key attr.name="startoffset" attr.type="int" for="edge" id="startoffset"/>
 <key attr.name="lineColSet" attr.type="string" for="edge" id="lineCols"/>
 <key attr.name="control" attr.type="string" for="edge" id="control"/>
 <key attr.name="assumption" attr.type="string" for="edge" id="assumption"/>
 <key attr.name="assumption.resultfunction" attr.type="string" for="edge" id="assumption.resultfunction"/>
 <key attr.name="assumption.scope" attr.type="string" for="edge" id="assumption.scope"/>
 <key attr.name="enterFunction" attr.type="string" for="edge" id="enterFunction"/>
 <key attr.name="returnFromFunction" attr.type="string" for="edge" id="returnFrom"/>
 <key attr.name="predecessor" attr.type="string" for="edge" id="predecessor"/>
 <key attr.name="successor" attr.type="string" for="edge" id="successor"/>
 <key attr.name="witness-type" attr.type="string" for="graph" id="witness-type"/>
 <key attr.name="creationtime" attr.type="string" for="graph" id="creationtime"/> 
 <graph edgedefault="directed">
  <data key="witness-type">{WITNESS_TYPE}</data>
  <data key="sourcecodelang">C</data>
  <data key="producer">Hornix-0.1.0</data>
  <data key="specification">CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )</data>
  <data key="programfile">{INPUT_FILE}</data>
  <data key="programhash">{SHA256SUM}</data>
  <data key="architecture">32bit</data>
  <data key="creationtime">{CREATION_TIME}+01:00</data>
 </graph>
</graphml>
'''



def run_z3(input_file, timeout = 900):
    # timeout in seconds, default 15 minutes
    #print ('running z3')
    return subprocess.run(['/usr/bin/z3', f"-T:{timeout}", input_file], capture_output=True, text=True)

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


def create_witness_v1(witness_type):
    global uuid

    data = list()
    # data['entry_type'] = ''
    # data['invariant'] = ''
    # data['content'] = ''

    output_file = Path(input_file).stem + '.graphml'
    # output_file =  Path(input_file).parent.joinpath('witness.graphml')
    uuid = uuid.uuid4()
    with open(input_cfile, 'rb') as f:
        sha256 = hashlib.sha256(f.read()).hexdigest()


    with open(output_file, 'wt') as f:
        f.write(WITNESS_TEMPLATE_V1.format(INPUT_FILE=input_cfile, SHA256SUM=sha256, CREATION_TIME=str(datetime.datetime.now().isoformat(timespec='seconds')), WITNESS_TYPE='correctness_witness' if witness_type == 'sat' else 'violation_witness'))



def create_witness_v2():
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
    #if output.strip() == 'sat':
    #    create_witness()
    create_witness_v1(output.strip())
