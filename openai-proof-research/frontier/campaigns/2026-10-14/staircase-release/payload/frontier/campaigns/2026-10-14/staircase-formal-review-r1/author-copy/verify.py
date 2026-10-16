#!/usr/bin/env python3
"""Read-only integrity verification. Copyright 2026 Myeongjin Kang. MIT."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    manifest = json.loads((HERE / 'output-manifest.json').read_text())
    expected = {row['path']: row for row in manifest['files']}
    actual = {p.relative_to(HERE).as_posix() for p in HERE.rglob('*') if p.is_file()
              and p.name != 'output-manifest.json'}
    check(actual == set(expected), 'Output inventory mismatch')
    for name, row in expected.items():
        path = HERE / name
        check(not path.is_symlink(), 'Unexpected output symlink: ' + name)
        check(path.stat().st_size == row['bytes'] and digest(path) == row['sha256'],
              'Output bytes/hash mismatch: ' + name)
    inputs = json.loads((HERE / 'input-manifest.json').read_text())
    for row in inputs['files']:
        path = ROOT / row['path']
        check(path.stat().st_size == row['bytes'] and digest(path) == row['sha256'],
              'Input changed since reading: ' + row['path'])
    candidate = next(row for row in inputs['files'] if row['role'] == 'frozen candidate')
    check(candidate['sha256'] == '6b2e14d58ef3e132a666e3cdc6dbb3a2caa53a514301dc30323b6b7cf652c179',
          'Frozen candidate differs from user brief')
    receipt = json.loads((HERE / 'validation.json').read_text())
    check(receipt['status'].startswith('PASS:'), 'No successful validation')
    check(receipt['source_sha256'] == digest(HERE / 'StaircaseSupport.lean'), 'Stale source receipt')
    check(not receipt['full_staircase_theorem_formalized'] and not receipt['acceptance_awarded'],
          'Invalid scope claim')
    check(receipt['lean_version'] == (HERE / 'logs/compiler-version.txt').read_text().strip(),
          'Compiler receipt mismatch')
    check(len(receipt['theorems']) == 16 and len(receipt['public_declarations']) == 20,
          'Declaration count changed')
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    check([r['name'] for r in receipt['runs']] == ['source', 'types-and-axioms', 'controls'],
          'Missing validation stages')
    for run, count in zip(receipt['runs'], [0, 20, 6]):
        path = HERE / 'logs' / (run['name'] + '.log')
        output = path.read_text()
        check(run['passed'] and run['exit_code'] == 0 and run['axiom_reports'] == count,
              'Failed validation stage: ' + run['name'])
        check(digest(path) == run['log_sha256'], 'Stale log receipt: ' + run['name'])
        check(not any(token in output for token in ['error:', 'warning:', 'sorryAx']),
              'Invalid compiler log: ' + run['name'])
        rows = re.findall(r'depends on axioms: \[([^\]]*)\]', output)
        check(len(rows) == count, 'Axiom report count mismatch')
        for row in rows:
            axioms = set(re.sub(r'\.\{[^}]*\}', '', row).split(', ')) - {''}
            check(axioms <= allowed, 'Nonstandard axiom: ' + row)
    for name in ['StaircaseSupport.lean', 'Checks.lean', 'Controls.lean']:
        check(not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', (HERE / name).read_text()),
              'Forbidden source token: ' + name)
    lock = json.loads((HERE / 'lake-manifest.json').read_text())
    check(receipt['dependency_revisions'] == {p['name']: p['rev'] for p in lock['packages']},
          'Dependency receipt differs from lock')
    print('PASS: output inventory/hashes, frozen inputs, compiler receipts, scope, and axiom reports')


if __name__ == '__main__':
    main()
