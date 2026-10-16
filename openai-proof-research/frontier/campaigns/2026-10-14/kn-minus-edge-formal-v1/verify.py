#!/usr/bin/env python3
"""Verify frozen hashes without rewriting manifests; optionally rebuild from source.
Copyright 2026 Myeongjin Kang. MIT.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def verify_records(base, records):
    for row in records:
        path = base / row['path']
        data = path.read_bytes()
        if row.get('verification') == 'historical_mutable_context':
            continue
        if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
            raise ValueError('Frozen hash/size mismatch: ' + str(path))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--payload-only', action='store_true', help='verify this directory without sibling research inputs')
    parser.add_argument('--rebuild', action='store_true')
    parser.add_argument('--lean', type=Path)
    parser.add_argument('--cache', type=Path)
    args = parser.parse_args()
    outputs = json.loads((HERE/'output-manifest.json').read_text())
    verify_records(HERE, outputs['files'])
    if not args.payload_only:
        inputs = json.loads((HERE/'input-manifest.json').read_text())
        verify_records((HERE/inputs['root']).resolve(), inputs['files'])
    receipt = json.loads((HERE/'logs/final/receipt.json').read_text())
    if not receipt['status'].startswith('PASS'):
        raise ValueError('Final build did not pass')
    for name, expected in receipt['source_sha256'].items():
        if hashlib.sha256((HERE/name).read_bytes()).hexdigest() != expected:
            raise ValueError('Source no longer matches the compiled source: ' + name)
    if receipt['full_crossing_theorem_formalized'] or receipt['independent_audit']:
        raise ValueError('Unexpected full-certificate or independent-audit claim')
    print(f"PASS {len(outputs['files'])} payload hash/size records; final receipt matches source")
    if not args.payload_only:
        required = sum(x.get('verification') != 'historical_mutable_context' for x in inputs['files'])
        context = len(inputs['files']) - required
        print(f"PASS {required} required external input hash/size records; {context} historical context record(s) retained")
    if args.rebuild:
        command = [sys.executable,'-B',str(HERE/'rebuild.py')]
        for flag in ['lean','cache']:
            value = getattr(args,flag)
            if value:
                command += ['--'+flag,str(value)]
        subprocess.run(command, cwd=HERE, check=True)
    print('Verification did not rewrite or reseal any frozen evidence')


if __name__ == '__main__':
    main()
