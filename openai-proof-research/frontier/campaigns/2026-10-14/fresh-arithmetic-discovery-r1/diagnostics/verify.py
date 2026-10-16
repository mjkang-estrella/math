#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License; see ../RIGHTS.md.
"""Read-only offline integrity and finite-identity replay; no proof gate."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
root = Path(__file__).resolve().parent.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


seal = json.loads((root / 'seal.json').read_text())
actual = sorted(str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()
                and p != root / 'seal.json')
assert actual == sorted(x['path'] for x in seal['files']), 'Owned inventory mismatch'
for row in seal['files']:
    assert digest(root / row['path']) == row['sha256'], row['path']

tree = json.loads((root / 'inputs/context/sources/preprints-tree.json').read_text())
entries = {x['path']: x for x in tree['tree'] if x['type'] == 'blob'}
assert not tree['truncated']
sources = json.loads((root / 'sources/manifest.json').read_text())
for row in sources:
    data = (root / row['copy']).read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    assert blob == row['git_blob'] == entries[row['path']]['sha'], row['path']
    assert hashlib.sha256(data).hexdigest() == row['sha256'], row['path']
    assert row['url'] == ('https://raw.githubusercontent.com/openai/math/'
                          'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' + row['path'])

for name in ['input-manifest.json', 'output-manifest.json']:
    manifest = json.loads((root / name).read_text())
    for row in manifest['files']:
        assert digest(root / row['path']) == row['sha256'], row['path']

for row in json.loads((root / 'inputs/context-manifest.json').read_text()):
    assert digest(root / row['copy']) == row['sha256'], row['copy']

reading = json.loads((root / 'reading.json').read_text())
for row in reading['passages']:
    lines = (root / row['path']).read_text().splitlines()
    a, b = row['lines_inclusive']
    assert 1 <= a <= b <= len(lines)
    passage = '\n'.join(lines[a - 1:b]).encode()
    assert hashlib.sha256(passage).hexdigest() == row['passage_sha256'], row['path']

spec = importlib.util.spec_from_file_location('arithmetic_finite_checks', root / 'diagnostics/check.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
results = module.run()
assert results == json.loads((root / 'diagnostics/results.json').read_text())
print(json.dumps({'integrity': 'PASS', 'upstream_blobs_verified': len(sources),
                  'owned_files': len(seal['files']) + 1,
                  'finite_checks': results['counts'],
                  'scope': 'Offline integrity and finite identities only. C4 and BG4 remain unresolved.'},
                 indent=2, sort_keys=True))
