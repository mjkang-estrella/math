#!/usr/bin/env python3
"""Read-only I46 replay: no writes, downloads, bytecode, or seal refresh."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import hashlib, json, os, subprocess

R = Path(__file__).resolve().parents[3]
S = R / 'frontier/sources/i46_quantitative_logarithmic_stability'
E = Path(__file__).resolve().parent
REPORT = R / 'frontier/iterations/i46-quantitative-logarithmic-stability.md'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
MUTABLE = {'README.md', 'frontier/README.md', 'frontier/TEN-FINDINGS.md',
           'frontier/iterations/README.md',
           'frontier/iterations/iteration46-quantitative-logarithmic-stability-task.json'}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def blob(p):
    b = p.read_bytes()
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()

def read(rel):
    return json.loads((S / rel).read_text())

seal = read('artifact-seal.json')
actual = {str(p.relative_to(R)) for base in (S, E) for p in base.rglob('*')
          if p.is_file() and p != S / 'artifact-seal.json'} | {str(REPORT.relative_to(R))}
expected = {row['path'] for row in seal['files']}
assert actual == expected, (actual - expected, expected - actual)
assert seal['pin'] == PIN
for row in seal['files']:
    p = R / row['path']
    assert sha(p) == row['sha256'] and p.stat().st_size == row['bytes'], row['path']

frozen = read('frozen-inputs.json')
assert {r['path'] for r in frozen if r['mutable']} == MUTABLE
drift = []
for row in frozen:
    assert sha(S / 'frozen' / row['path']) == row['sha256'], row['path']
    live = R / row['path']
    if not live.exists() or sha(live) != row['sha256']:
        if row['mutable']:
            drift.append(row['path'])
        else:
            raise AssertionError('Immutable dependency changed: ' + row['path'])
task = read('frozen/frontier/iterations/iteration46-quantitative-logarithmic-stability-task.json')
assert (S / 'brief.txt').read_text() == task['brief']

historical = []
for row in read('prior-seals.json'):
    frozen_seal = S / 'frozen' / row['path']
    assert sha(frozen_seal) == sha(R / row['path']) == row['sha256']
    old = json.loads(frozen_seal.read_text())
    assert len(old['files']) == row['artifacts']
    for item in old['files']:
        assert sha(R / item['path']) == item['sha256'], item['path']
    historical.append({'tag': row['tag'], 'unchanged_artifacts': len(old['files'])})

inv = read('frozen/sources/preprints-tree.json')
assert not inv['truncated'] and len(inv['tree']) == 13223
blobs = {r['path']: r['sha'] for r in inv['tree'] if r['type'] == 'blob'}
papers = {r['path'].split('/')[1] for r in inv['tree'] if r['path'].startswith('preprints/')}
assert len(papers) == 749
manifest = read('frozen/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json')
assert manifest['pin'] == PIN
C = R / 'frontier/sources/i14_spectral_width_novelty_r3/corpus'
listed = subprocess.run(['rg', '--files', '--no-ignore', str(C)], check=True,
                        capture_output=True, text=True).stdout.splitlines()
assert {str(Path(p).relative_to(C)) for p in listed} == {r['path'] for r in manifest['files']}
assert len(listed) == 9340
for row in manifest['files']:
    p = C / row['path']
    assert p.stat().st_size == row['bytes'] and sha(p) == row['sha256'], row['path']
    assert blob(p) == row['git_blob'] == blobs[row['path']], row['path']
for row in read('corpus-search.json'):
    result = subprocess.run(['rg', '--no-ignore', '-n', '-i', row['pattern'], str(C)],
                            capture_output=True, text=True)
    assert result.returncode == row['returncode']
    assert sorted(result.stdout.splitlines()) == sorted((S / row['output']).read_text().splitlines())

selected = read('inherited-selected-manifest.json')
assert selected['pin'] == PIN
for row in selected['files']:
    p = S / 'pinned' / row['path']
    assert sha(p) == row['sha256'] and blob(p) == row['git_blob'] == blobs[row['path']]
for row in read('source-contracts.json'):
    source = (S / 'pinned' / row['path']).read_text()
    for label in row['labels']:
        assert '{' + label + '}' in source, label
for row in read('read-passages.json'):
    p = S / row['path']
    assert sha(p) == row['sha256']
    lines = p.read_text().splitlines()
    extract = '\n'.join(f'{i}: {lines[i-1]}' for a, b in row['ranges'] for i in range(a, b+1)) + '\n'
    assert extract == (S / row['extract']).read_text(), row['path']
for row in read('external-contracts.json'):
    assert sha(S / row['file']) == row['sha256']
responses = read('responses.json')
for row in responses + read('inherited-response-bindings.json'):
    assert sha(S / row['file']) == row['sha256'], row['file']
for name in ('reduction', 'tensor', 'variance'):
    p = S / f'fresh/{name}-fresh.tex'
    q = S / f'pinned/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/build/{name}.tex'
    assert p.read_bytes() == q.read_bytes()
for row in read('versions.json'):
    p = S / row['file']
    assert sha(p) == row['sha256']
    assert row['canonical_version_url'] in p.read_text()
    assert all(line in p.read_text() for line in row['submission_lines'])

run = subprocess.run([sys.executable, str(E / 'check.py')], check=True, capture_output=True,
                     text=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
assert run.stdout == (E / 'check-output.json').read_text()
diagnostic = json.loads(run.stdout)
assert diagnostic['status'] == 'PASS' and diagnostic['exact_assertions'] == 3319
print(json.dumps({
    'status': 'PASS',
    'scope': 'Read-only evidence integrity and finite exact diagnostics; no analytic acceptance or priority certification.',
    'sealed_artifacts': len(seal['files']), 'frozen_inputs': len(frozen),
    'mutable_shared_ledgers': 4, 'mutable_orchestration_records': 1, 'mutable_input_drift': drift,
    'historical_seals': historical, 'tree_entries': 13223, 'manuscripts': 749,
    'corpus_files': 9340, 'corpus_searches_replayed': len(read('corpus-search.json')),
    'selected_pinned_files': len(selected['files']), 'fresh_responses': len(responses),
    'successful_fresh_responses': sum(bool(r['ok']) for r in responses),
    'inherited_response_bindings': len(read('inherited-response-bindings.json')),
    'read_passage_records': len(read('read-passages.json')),
    'exact_assertions': diagnostic['exact_assertions'], 'polygon_cases': diagnostic['polygon_cases'],
    'proof_status': 'P10 author proof only; all-dimensional finite-power target open in this report'
}, indent=2, sort_keys=True))
