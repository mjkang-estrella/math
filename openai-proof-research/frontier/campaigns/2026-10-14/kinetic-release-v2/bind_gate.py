#!/usr/bin/env python3
"""Parent-only config builder from an existing authenticated final disposition.
Copyright 2026 Myeongjin Kang; MIT. Does not create a verdict or reviewer identity.
"""
from pathlib import Path
import argparse
import json
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from release_common import (FROZEN_HASHES, MANUSCRIPT, PARENT, REVIEW, check_record,
    decode_json, discover_root, manifest_records, read_regular, record, safe_name,
    validate_gate)


def build_config(root, parent_path, parent_sha256, artifact_paths):
    raw = read_regular(root, parent_path)
    parent = record(parent_path, raw)
    if parent['sha256'] != parent_sha256:
        raise ValueError('Parent disposition differs from independently trusted hash')
    disposition = decode_json(raw)
    if not isinstance(disposition, dict) or disposition.get('schema') != 'kinetic-manuscript-parent-disposition-v2':
        raise ValueError('An actual corrected-edition parent disposition is required')
    gate = {'schema':'kinetic-release-gate-v2', 'state':'integrated',
            'manuscript_path':MANUSCRIPT, 'bound_manuscript':FROZEN_HASHES,
            'parent_disposition':parent, 'review_artifacts':[]}
    for name in ['review', 'review_manifest', 'reviewer_record', 'reviewer', 'reviewer_identity_basis']:
        gate[name] = disposition[name]
    rows = manifest_records(decode_json(check_record(root, gate['review_manifest'])), REVIEW)
    for path in artifact_paths:
        safe_name(path)
        if path not in rows:
            raise ValueError('Requested artifact is not a final-review manifest member: '+path)
        gate['review_artifacts'].append(rows[path])
    validate_gate(root, gate, FROZEN_HASHES, True, parent_sha256)
    return gate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project-root', type=Path)
    parser.add_argument('--parent-disposition', required=True, help='existing project-relative final parent JSON')
    parser.add_argument('--parent-disposition-sha256', required=True)
    parser.add_argument('--artifact', action='append', default=[], help='actual project-relative final-review manifest member')
    parser.add_argument('--output', required=True, help='new project-relative parent config JSON')
    args = parser.parse_args()
    root = args.project_root or discover_root(Path(__file__).resolve().parent)
    output = safe_name(args.output)
    if (not args.output.startswith(PARENT+'/') or 'manuscript' not in output.name
            or output.suffix != '.json'):
        parser.error('Output must be a new manuscript JSON under kinetic-parent/')
    gate = build_config(root, args.parent_disposition, args.parent_disposition_sha256, args.artifact)
    destination = root.joinpath(*output.parts)
    if root.absolute() != root.resolve() or any(p.is_symlink() for p in [destination,*destination.parents]):
        raise ValueError('Symlink output path is not allowed')
    if not destination.parent.is_dir():
        raise ValueError('Output parent must already exist')
    # One exclusive write, after authenticating all actual parent/review inputs.
    data = (json.dumps(gate,indent=2)+'\n').encode()
    with destination.open('xb') as stream:
        stream.write(data)
    print(json.dumps(record(args.output,data),indent=2))


if __name__ == '__main__':
    main()
