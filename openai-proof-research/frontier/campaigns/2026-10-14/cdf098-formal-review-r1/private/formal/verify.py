#!/usr/bin/env python3
"""Copyright 2026 Myeongjin Kang. MIT. Externally anchored integrity only."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--anchor', required=True)
    ap.add_argument('--check-inputs', action='store_true')
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    raw = (root / 'output-manifest.json').read_bytes()
    require(sha(raw) == args.anchor, 'external manifest anchor mismatch')
    manifest = json.loads(raw)
    expected = {}
    for item in manifest['files']:
        name = item['path']; p = PurePosixPath(name)
        require(str(p) == name and not p.is_absolute() and '..' not in p.parts, 'noncanonical path')
        require(name != 'output-manifest.json' and name not in expected, 'duplicate/reserved path')
        require(p.parts[0] != '.replays', 'future replay is not sealed input')
        expected[name] = item
    files, dirs = set(), set()
    for path in root.rglob('*'):
        rel = path.relative_to(root)
        require(not path.is_symlink(), 'symlink')
        if rel.parts[0] == '.replays':
            continue
        if path.is_dir():
            dirs.add(rel.as_posix())
        else:
            require(path.is_file(), 'special file')
            if rel.as_posix() != 'output-manifest.json':
                files.add(rel.as_posix())
    require(files == set(expected), 'exact file membership mismatch')
    require(dirs == set(manifest['directories']) and len(dirs) == len(manifest['directories']), 'exact directory membership mismatch')
    for name, item in expected.items():
        data = (root / name).read_bytes()
        require(len(data) == item['bytes'] and sha(data) == item['sha256'], 'changed payload: ' + name)
    inputs = json.loads((root / 'input-manifest.json').read_text())
    input_hashes = {}
    for item in inputs:
        data = (root / item['snapshot']).read_bytes()
        require(len(data) == item['bytes'] and sha(data) == item['sha256'], 'snapshot mismatch')
        input_hashes[item['original_path']] = item['sha256']
        if args.check_inputs:
            data = (root / item['original_path']).read_bytes()
            require(len(data) == item['bytes'] and sha(data) == item['sha256'], 'external input mismatch')
    anchors = {
        '../fresh-parent-discovery-r8/manifest.json': 'f417cfd409e18a34c97f488fb10ebfa25f1b09b5fc4ff323c53c71cf71262c85',
        '../fresh-parent-discovery-r8/original-scope.md': 'bb115b9c504b9e5d8e3f62d841bc16095049f23719a47eb13d18d253ed1741c5',
        '../fresh-parent-discovery-r8/candidate.md': '24c5d7055f19b48bac26451a87896845756865eeeba5d0502e1f7982ccb6f39a',
        '../cdf098-proof-r1/manifest.json': '543aba870bfb7237dcd95e2d03fd40e644350b7acbc9aa43cb90c08553a80dda',
        '../cdf098-contribution-r1/manifest.json': '42befbcdc270f6802d47080dfba86ef105dcd9316a237324eb0a4a5355f4c691'}
    require(all(input_hashes.get(k) == v for k, v in anchors.items()), 'frozen input anchor mismatch')
    source = (root / 'CDFLocal.lean').read_text()
    names = re.findall(r'^(?:noncomputable )?(?:def|theorem) (\w+)', source, re.M)
    thms = re.findall(r'^theorem (\w+)', source, re.M)
    controls = re.findall(r'^theorem (\w+)', (root / 'Controls.lean').read_text(), re.M)
    coverage = json.loads((root / 'coverage.json').read_text())
    require(coverage['full_CDF098_formalized'] is False and coverage['independent_formal_audit'] is False, 'scope/independence drift')
    require(sorted(thms) == sorted(n for g in coverage['groups'] for n in g['theorems']), 'coverage mismatch')
    require((len(thms), len(names), len(controls)) == (30, 39, 11), 'declaration counts changed')
    pins = {x['name']: x['rev'] for x in json.loads((root / 'lake-manifest.json').read_text())['packages']}
    require(pins['mathlib'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612', 'mathlib pin mismatch')
    for label in ['first-build', 'clean-rebuild']:
        folder = root / 'logs' / label
        receipt = json.loads((folder / 'receipt.json').read_text())
        require(receipt['status'].startswith('PASS scoped source build'), 'build failed')
        require(receipt['previous_support_objects_used'] is False and receipt['full_CDF098_theorem_formalized'] is False, 'build scope mismatch')
        require(receipt['dependency_revisions'] == pins, 'dependency mismatch')
        require('4.34.1' in receipt['lean_version'] and '5045d0056413266e57c625dcd7c365b10e377c52' in receipt['lean_version'], 'compiler mismatch')
        for name, digest in receipt['source_sha256'].items():
            require(sha((root / name).read_bytes()) == digest, 'build/source mismatch')
        require(receipt['support_declarations'] == names and receipt['support_theorems'] == thms and receipt['control_theorems'] == controls, 'missing declarations')
        for report, namespace, entries in [(receipt['axiom_reports'], 'CDFLocal', names), (receipt['control_axiom_reports'], 'CDFControls', controls)]:
            require(set(report) == {namespace + '.' + n for n in entries}, 'missing axiom report')
            require(all(set(v) <= {'propext', 'Classical.choice', 'Quot.sound'} for v in report.values()), 'extra axiom')
        for run in receipt['runs']:
            require(run['exit_code'] == 0, 'failed run')
            for suffix in ['stdout', 'stderr']:
                data = (folder / (run['name'] + '.' + suffix)).read_bytes()
                require(sha(data) == run[suffix + '_sha256'], 'run log mismatch')
                require(not re.search(r'\b(?:SOME\s+FAIL|FAIL(?:ED)?|Traceback)\b|\berror:|warning:', data.decode(), re.I), 'failure in successful log')
    for name in ['types-axioms.stdout', 'example-types-axioms.stdout']:
        require((root / 'logs/first-build' / name).read_bytes() == (root / 'logs/clean-rebuild' / name).read_bytes(), 'type/axiom output drift')
    folder = root / 'logs/mutations'; mr = json.loads((folder / 'receipt.json').read_text())
    require(mr['source_sha256'] == sha((root / 'CDFLocal.lean').read_bytes()) and len(mr['cases']) == 6, 'mutation linkage')
    for case in mr['cases']:
        data = (folder / (case['case'] + '.stdout')).read_bytes()
        text = data.decode() + (folder / (case['case'] + '.stderr')).read_text()
        require(case['exit_code'] != 0 and case['result'] == 'EXPECTED_PROOF_REJECTION' and sha(data) == case['stdout_sha256'], 'bad mutation result')
        require(any(s in text for s in ['linarith failed', 'unsolved goals', 'omega could not prove']), 'not mathematical rejection')
        require(not any(s in text for s in ['unknown module', 'unexpected token', 'Unknown identifier', 'Type mismatch', 'Application type mismatch']), 'invalid mutation control')
    folder = root / 'logs/runner-control'; rr = json.loads((folder / 'receipt.json').read_text())
    require(rr['child_exit'] == 0 and rr['wrapper_exit'] != 0 and (folder / 'child.stdout').read_text() == 'SOME FAIL\n' and 'exit=0' in (folder / 'wrapper.stderr').read_text(), 'runner control failed')
    print(json.dumps({'status': 'PASS integrity only', 'payloads': len(expected), 'snapshot_inputs': len(inputs), 'external_inputs_checked': args.check_inputs, 'full_CDF098_formalized': False, 'independent_formal_audit': False, 'count_change': 0}))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as exc:
        raise SystemExit('REJECT: ' + str(exc))
