"""Offline integrity and exact diagnostic verifier. Not a proof checker."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[3]
S = ROOT / 'frontier/sources/i36_harmonic_analysis_discovery'
X = Path(__file__).resolve().parent
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
sha = lambda b: hashlib.sha256(b).hexdigest()
read = lambda p: json.loads(p.read_text())


def check_row(row, path_key='path', hash_key='sha256'):
    p = ROOT / row[path_key]
    b = p.read_bytes()
    assert sha(b) == row[hash_key], ('SHA mismatch', str(p))
    if path_key == 'path' and 'bytes' in row:
        assert len(b) == row['bytes'], ('length mismatch', str(p))
    return b


seal = read(S / 'artifact-seal.json')
assert seal['pin'] == PIN
for row in seal['files']:
    check_row(row)
excluded = {S / 'artifact-seal.json', X / 'verification.json'}
actual = {str(p.relative_to(ROOT)) for directory in (S, X)
          for p in directory.rglob('*') if p.is_file() and p not in excluded
          and '__pycache__' not in p.parts}
actual.add('frontier/iterations/i36-harmonic-analysis-discovery.md')
assert actual == {r['path'] for r in seal['files']}, 'unsealed or missing owned file'

drift = []
inputs = read(S / 'input-manifest.json')
for row in inputs:
    p = ROOT / row['path']
    current = sha(p.read_bytes()) if p.exists() else None
    if current != row['sha256']:
        assert row['mutable'], ('immutable dependency drift', row['path'])
        drift.append({'path': row['path'], 'baseline': row['sha256'], 'current': current})
    frozen = S / 'frozen' / row['path']
    if frozen.exists():
        assert sha(frozen.read_bytes()) == row['sha256']

tree = read(ROOT / 'sources/preprints-tree.json')
assert tree['truncated'] is False
entries = {r['path']: r for r in tree['tree']}
names = sorted({r['path'].split('/')[1] for r in tree['tree']
                if r['path'].startswith('preprints/')})
assert len(names) == 749
assert names == (S / 'complete-manuscript-inventory.txt').read_text().splitlines()
assert all(r['files_scanned'] == 9340 for r in read(S / 'corpus-search-audit.json'))
assert PIN in (ROOT / 'sources/upstream.json').read_text()

pinned = read(S / 'pinned-manifest.json')
for row in pinned:
    b = check_row(row, 'local')
    assert len(b) == row['bytes']
    blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
    assert blob == row['git_blob'] == entries[row['path']]['sha']
    assert row['url'] == f'https://raw.githubusercontent.com/openai/math/{PIN}/' + row['path']

passages = read(S / 'read-passages.json') + read(S / 'literature/read-passages.json')
for row in passages:
    p = ROOT / row['path']
    if 'first_line' in row:
        block = ''.join(p.read_text().splitlines(keepends=True)
                        [row['first_line']-1:row['last_line']]).encode()
        assert sha(block) == row['sha256'], ('passage mismatch', row['path'])
    else:
        check_row(row)

contracts = read(S / 'source-contracts.json')
for row in contracts:
    p = ROOT / row['path']
    assert sha(p.read_bytes()) == row['source_sha256']
    block = '\n'.join(p.read_text().splitlines()[row['first_line']-1:row['last_line']])
    assert row['text'] in block
    assert sha(row['text'].encode()) == row['sha256']

retrievals = read(S / 'literature/manifest.json') + read(S / 'literature/extra-manifest.json')
retained = 0
for row in retrievals:
    if 'path' in row and 'sha256' in row:
        check_row(row)
        retained += 1
    if 'text_path' in row and 'text_sha256' in row:
        check_row(row, 'text_path', 'text_sha256')
for row in read(S / 'literature/version-record.json'):
    check_row(row)

run = subprocess.run([sys.executable, str(X / 'checks.py')],
                     capture_output=True, check=True)
assert run.stdout == (X / 'checks.json').read_bytes(), 'diagnostics not byte reproducible'
checks = json.loads(run.stdout)
assert checks['status'] == 'PASS'
result = {
    'status': 'PASS',
    'scope': 'Evidence integrity and exact finite diagnostics only; universal proof and significance require independent reviews.',
    'pin': PIN,
    'sealed_files': len(seal['files']),
    'manuscripts': len(names),
    'searched_cache_files_recorded': 9340,
    'pinned_files': len(pinned),
    'source_contracts': len(contracts),
    'read_passages_and_visual_pages': len(passages),
    'retained_primary_responses': retained,
    'exact_diagnostic_counts': checks['counts'],
    'mutable_shared_ledger_drift': drift,
}
output = json.dumps(result, indent=2, sort_keys=True) + '\n'
(X / 'verification.json').write_text(output)
print(output, end='')
