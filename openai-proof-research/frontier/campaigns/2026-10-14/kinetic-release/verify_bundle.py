#!/usr/bin/env python3
"""Verify an extracted tree, without modifying it. Myeongjin Kang, 2026; MIT."""
from pathlib import Path
import argparse
import json
import os
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from release_common import (FROZEN_HASHES, check_record, check_freeze, discover_root,
    excluded_payload, read_json, read_regular, sha, validate_gate, run_finite_checks)
from assemble import collect


def verify(root, preparation=False, expected_manifest_sha256=None):
    raw = read_regular(root, 'BUNDLE-MANIFEST.json')
    if expected_manifest_sha256 is not None and sha(raw) != expected_manifest_sha256:
        raise ValueError('Manifest differs from independently expected hash')
    manifest = json.loads(raw)
    if manifest.get('schema') != 'kinetic-local-bundle-v1':
        raise ValueError('Unknown bundle schema')
    indexed = {}
    for row in manifest['files']:
        name = row['path']
        if name in indexed or name == 'BUNDLE-MANIFEST.json' or excluded_payload(name):
            raise ValueError('Duplicate or excluded member: '+name)
        indexed[name] = check_record(root, row)
    expected = set(indexed) | {'BUNDLE-MANIFEST.json'}
    expected_dirs = {str(p) for name in expected for p in Path(name).parents if str(p) != '.'}
    actual = set()
    for directory, dirs, files in os.walk(root, followlinks=False):
        for name in dirs:
            path = Path(directory)/name
            relative = path.relative_to(root).as_posix()
            if path.is_symlink() or relative not in expected_dirs:
                raise ValueError('Unexpected directory or symlink: '+relative)
        for name in files:
            path = Path(directory)/name
            relative = path.relative_to(root).as_posix()
            # Includes FIFOs/devices and file symlinks, even if unlisted.
            read_regular(root, relative)
            actual.add(relative)
    if actual != expected:
        raise ValueError('Extracted membership differs: '+repr(sorted(actual ^ expected)))
    if manifest.get('bound_manuscript') != FROZEN_HASHES:
        raise ValueError('Bundle freeze mismatch')
    check_freeze(root)
    gate = read_json(root, manifest['gate_path'])
    if manifest.get('gate_state') != gate.get('state'):
        raise ValueError('Manifest/config gate mismatch')
    required = validate_gate(root, gate, FROZEN_HASHES, not preparation,
                             manifest.get('trusted_parent_disposition_sha256'))
    if any(name not in indexed or indexed[name] != data for name, data in required.items()):
        raise ValueError('Gate records absent from bundle inventory')
    selected, _ = collect(root, manifest['gate_path'],
                           manifest.get('trusted_parent_disposition_sha256'), not preparation)
    if selected != indexed:
        raise ValueError('Bundle inventory differs from the explicit allowlists and gate records')
    results = run_finite_checks(root)
    if results != manifest['finite_checks']:
        raise ValueError('Finite-check manifest differs from rerun')
    return {'status':('PREPARATION CHECK PASSED; GATE PENDING' if gate['state']=='pending'
                      else 'BUNDLE INTEGRITY AND FINITE CHECKS PASSED'),
            'files':len(indexed), 'gate_state':gate['state'], 'finite_checks':results,
            'full_analytic_or_Lean_certificate':False, 'tree_modified':False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path)
    parser.add_argument('--manifest-sha256')
    parser.add_argument('--preparation', action='store_true',
                        help='explicitly permit a pending-gate dry-run tree; never release approval')
    args = parser.parse_args()
    root = args.root or discover_root(Path(__file__).resolve().parent)
    print(json.dumps(verify(root, args.preparation, args.manifest_sha256), indent=2))
