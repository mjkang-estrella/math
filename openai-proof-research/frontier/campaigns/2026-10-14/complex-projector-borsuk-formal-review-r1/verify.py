#!/usr/bin/env python3
"""Copyright 2026 Myeongjin Kang. MIT. Anchored identity, not a proof checker."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re

AUTHOR_ANCHOR = '28429901ed26db71aaa1bc3b4b7c62c1f2c38f945510e04ba4e4f48eb5893700'
SOURCE = '8c6863344596404bf7f8e13e341972510f3ad7d4fa63308a9d31872a9d947cab'
COVERAGE = '705df89da3ec6ef20eb0013d3c24a2839b6f340357d52bb23bc30a79470871d9'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def canonical(name):
    p = PurePosixPath(name)
    require(str(p) == name and not p.is_absolute() and '..' not in p.parts
            and name not in ('', '.'), 'noncanonical path')
    return p


def verify_manifest(root, filename, anchor, exclude_replays=False):
    raw = (root / filename).read_bytes()
    require(sha(raw) == anchor, 'external manifest anchor mismatch')
    manifest = json.loads(raw)
    entries = {}
    for item in manifest['files']:
        name = item['path']; p = canonical(name)
        require(name != filename and name not in entries, 'duplicate/reserved path')
        require(not exclude_replays or p.parts[0] != '.replays', 'sealed replay input')
        entries[name] = item
    actual, dirs = set(), set()
    for path in root.rglob('*'):
        rel = path.relative_to(root)
        require(not path.is_symlink(), 'symlink')
        if exclude_replays and rel.parts[0] == '.replays':
            continue
        if path.is_dir():
            dirs.add(rel.as_posix())
        else:
            require(path.is_file(), 'special file')
            if rel.as_posix() != filename:
                actual.add(rel.as_posix())
    require(actual == set(entries), 'exact file membership mismatch')
    require(dirs == set(manifest['directories']), 'exact directory membership mismatch')
    require(len(manifest['directories']) == len(dirs), 'duplicate directory')
    for name, item in entries.items():
        b = (root / name).read_bytes()
        require(len(b) == item['bytes'] and sha(b) == item['sha256'], 'changed payload: ' + name)
    return len(entries)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--anchor', required=True)
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    total = verify_manifest(root, 'output-manifest.json', args.anchor)
    author = root / 'private/author'
    count = verify_manifest(author, 'output-manifest.json', AUTHOR_ANCHOR, True)
    require(sha((author / 'BorsukLocal.lean').read_bytes()) == SOURCE, 'source anchor mismatch')
    require(sha((author / 'coverage.json').read_bytes()) == COVERAGE, 'coverage anchor mismatch')
    require(json.loads((author / 'coverage.json').read_text())['full_B8C_formalized'] is False, 'scope drift')
    rows = json.loads((root / 'input-manifest.json').read_text())['externally_supplied_anchors_and_author_inputs']
    for row in rows:
        canonical(row['path']); data = (root / row['path']).read_bytes()
        require(len(data) == row['bytes'] and sha(data) == row['sha256'], 'input mismatch')
    for row in json.loads((author / 'input-manifest.json').read_text()):
        p = (author / row['path']).resolve()
        require(p.is_relative_to(root), 'external input outside review snapshot')
        data = p.read_bytes()
        require(len(data) == row['bytes'] and sha(data) == row['sha256'], 'author input mismatch')
    build = author / '.replays/independent-build'
    receipt = json.loads((build / 'receipt.json').read_text())
    require(receipt['status'] == 'PASS scoped source build, exact types, standard axioms and semantic controls', 'build failed')
    require(receipt['previous_support_objects_used'] is False and receipt['full_B8C_theorem_formalized'] is False, 'build scope/object mismatch')
    require('4.34.1' in receipt['lean_version'] and '5045d0056413266e57c625dcd7c365b10e377c52' in receipt['lean_version'], 'compiler mismatch')
    lock = json.loads((author / 'lake-manifest.json').read_text())
    pins = {x['name']: x['rev'] for x in lock['packages']}
    require(receipt['dependency_revisions'] == pins and pins['mathlib'] == 'd13f23b723b8a846827a245b89c10fc7d3f11612', 'dependency mismatch')
    for name, digest in receipt['source_sha256'].items():
        canonical(name); require(sha((author / name).read_bytes()) == digest, 'fresh build/source mismatch')
    require(len(receipt['support_theorems']) == 16 and len(receipt['support_declarations']) == 19 and len(receipt['control_theorems']) == 13, 'declaration count mismatch')
    for reports, namespace, names in [(receipt['axiom_reports'], 'BorsukLocal', receipt['support_declarations']), (receipt['control_axiom_reports'], 'BorsukControls', receipt['control_theorems'])]:
        require(set(reports) == {namespace + '.' + n for n in names}, 'missing axiom report')
        require(all(set(v) <= {'propext', 'Classical.choice', 'Quot.sound'} for v in reports.values()), 'extra axiom')
    for run in receipt['runs']:
        require(run['exit_code'] == 0, 'run failed')
        for suffix in ['stdout', 'stderr']:
            data = (build / (run['name'] + '.' + suffix)).read_bytes()
            require(sha(data) == run[suffix + '_sha256'], 'run log mismatch')
            require(not re.search(r'\b(?:SOME\s+FAIL|FAIL(?:ED)?|Traceback)\b|\berror:|warning:', data.decode(), re.I), 'successful run contains failure')
    mutations = author / '.replays/independent-mutations'
    mr = json.loads((mutations / 'receipt.json').read_text())
    require(mr['source_sha256'] == SOURCE and len(mr['cases']) == 5 and mr['full_B8C_formalized'] is False, 'mutation/source mismatch')
    for case in mr['cases']:
        data = (mutations / (case['case'] + '.stdout')).read_bytes()
        text = data.decode() + (mutations / (case['case'] + '.stderr')).read_text()
        require(sha(data) == case['stdout_sha256'] and case['exit_code'] != 0 and case['result'] == 'EXPECTED_PROOF_REJECTION', 'mutation result mismatch')
        require('linarith failed' in text or 'unsolved goals' in text, 'not a mathematical rejection')
        require(not any(s in text for s in ['unknown module', 'unexpected token', 'Unknown identifier', 'Type mismatch', 'Application type mismatch']), 'invalid mutation control')
    runner = root / 'runner-control'
    rr = json.loads((runner / 'receipt.json').read_text())
    require(rr['child_exit'] == 0 and rr['wrapper_exit'] != 0 and (runner / 'printed-failure.stdout').read_text() == 'SOME FAIL\n' and 'exit=0' in (runner / 'wrapper.stderr').read_text(), 'failure marker control mismatch')
    print(json.dumps({'status': 'PASS identity and retained independent-run linkage only', 'review_payloads': total, 'author_payloads': count, 'verdict': 'PASS_SCOPED_SUPPORT', 'full_B8C_formalized': False, 'count_change': 0}))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as exc:
        raise SystemExit('REJECT: ' + str(exc))
