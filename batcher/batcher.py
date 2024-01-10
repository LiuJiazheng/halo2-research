import argparse
import os
import json
from typing import TypedDict, Optional

COLUMN_NAME = "img_col"

class TemplateCol(TypedDict):
    name: str
    proof_idx: int
    column_name: str

class TemplateInstance(TypedDict):
    name: str
    proof_idx: int
    group_idx: int

class EquivalencePair(TypedDict):
    source: TemplateCol
    target: TemplateCol

class AbsorbPair(TypedDict):
    instance_idx: TemplateInstance
    target: TemplateCol

def compose_first_dsl(proof_name: str) -> dict:
    expose: TemplateCol = {
        "name": proof_name,
        "proof_idx": 0,
        "column_name": COLUMN_NAME,
    }
    sepc = {
        "equivalents": [],
        "expose": [expose],
        "absorb": [],
    }
    return sepc

def compose_middle_dsl(proof_name: str, proof_idx: int, group_idx: int) -> dict:
    instance: TemplateInstance = {
        "name": proof_name,
        "proof_idx": proof_idx,
        "group_idx": group_idx,
    }
    target: TemplateCol = {
        "name": proof_name,
        "proof_idx": proof_idx,
        "column_name": COLUMN_NAME,
    }
    absorb: AbsorbPair = {
        "instance_idx": instance,
        "target": target,
    }
    expose = target.copy()
    sepc = {
        "equivalents": [],
        "expose": [expose],
        "absorb": [absorb],
    }
    return sepc

def compose_last_dsl(proof_name: str, proof_idx: int, group_idx: int) -> dict:
    instance: TemplateInstance = {
        "name": proof_name,
        "proof_idx": proof_idx,
        "group_idx": group_idx,
    }
    target: TemplateCol = {
        "name": proof_name,
        "proof_idx": proof_idx,
        "column_name": COLUMN_NAME,
    }
    absorb: AbsorbPair = {
        "instance_idx": instance,
        "target": target,
    }
    sepc = {
        "equivalents": [],
        "expose": [],
        "absorb": [absorb],
    }
    return sepc

def write_json(json_dict: dict, file_name: str) -> None:
    json_str = json.dumps(json_dict)
    with open(file_name, mode='w') as f:
        f.write(json_str)
    
def main():
    parser = argparse.ArgumentParser(description='Batcher')
    parser.add_argument('name', help='Proof Serires Name')
    parser.add_argument('length', help='Proof Serires Length')
    args = parser.parse_args()
    name = str(args.name)
    batch_name = "batch_" + name
    length = int(args.length)
    for i in range(length):
        if i == 0:
            write_json(compose_first_dsl(name), batch_name + "_" + str(i) + ".json")
        elif i == length - 1:
            write_json(compose_last_dsl(name, i, i), batch_name + "_" + str(i) + ".json")
        else:
            write_json(compose_middle_dsl(name, i, i), batch_name + "_" + str(i) + ".json")

    # Your code here

if __name__ == '__main__':
    main()
