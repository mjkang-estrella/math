#!/usr/bin/env python3
"""Read-only verification of the notified r162i packet; no mathematical gate."""
from pathlib import Path
import hashlib
import json
import stat
import subprocess

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'discovery-arithmetic-r162i-parent'
r = b / 'fresh-arithmetic-discovery-r162i'
m = r / 'packet/private'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def load(path):
    return json.loads(path.read_bytes())

anchors = {
    'packet/FINAL.md': '31fb8292514f5a38d053645b01c67cf7c498068f291c10c8f3d3f7cdcd8ed011',
    'MANIFEST.json': '8dca60ab758e17955fd3fb8e7adcf132e930389a39eee041421412941cae4d6a',
    'REPORT.md': '9dd502703dff0279110dd16ca6317c25c5bf3c9204f33b0388c85eee7da382a9',
}
for rel, sha in anchors.items():
    assert digest((r / rel).read_bytes()) == sha
run = subprocess.run([
    'python', '-I', '-B', str(r / 'packet/verify_packet.py'), str(r),
    '--final-sha', anchors['packet/FINAL.md'],
    '--manifest-sha', anchors['MANIFEST.json'],
    '--report-sha', anchors['REPORT.md'],
], check=True, capture_output=True, text=True)
result = json.loads(run.stdout)
assert result['artifact_match'] and not result['mathematical_gate']
tree_data = (p / 'sources/preprints-tree.json').read_bytes()
assert digest(tree_data) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = load(p / 'sources/preprints-tree.json')
assert len(tree['tree']) == 13223 and not tree['truncated']
by_path = {e['path']: e for e in tree['tree']}
auth = load(m / 'canonical-authentication.json')
assert len(auth) == 19
canonical_bytes = 0
for e in auth:
    original = by_path[e['path']]
    assert all(e[k] == original[k] for k in ['path', 'mode', 'type', 'sha', 'size'])
    data = (p / e['local']).read_bytes()
    assert len(data) == e['size'] and digest(data) == e['sha256']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == e['sha']
    canonical_bytes += len(data)
completed = load(m / 'completed-reading.json')
for e in completed:
    source, copied = p / e['original'], p / e['local']
    data = source.read_bytes()
    assert data == copied.read_bytes() and len(data) == e['bytes'] and digest(data) == e['sha256']
for e in load(m / 'history-reading.json'):
    with (p / e['original']).open('rb') as f:
        f.seek(e['extent'][0]); data = f.read(e['extent'][1] - e['extent'][0])
    assert digest(data) == e['sha256']
primary = load(m / 'primary-reading.json')
for e in primary:
    data = (p / e['local']).read_bytes()
    if 'bytes' in e:
        assert len(data) == e['bytes'] and digest(data) == e['sha256']
    else:
        # The visual-reading row has no whole-file hash fields; use the
        # exact PDF binding actually disclosed in READING-ISOLATION.md.
        assert e['local'].endswith('/Shmerkin-JEMS-2023.pdf')
        assert len(data) == 561433
        assert digest(data) == '48bd946e855401da01b41d40fdf909dd07e24501c8b838ba5aa2d57c9d40d3ac'
controls = load(m / 'control-results.json')
assert len(controls) == 5
assert all((e['returncode'] == 0) == e['expected_success'] for e in controls)
before = load(o / 'private/root-before.json')
after = {f.relative_to(r).as_posix(): {
    'bytes': f.stat().st_size, 'sha256': digest(f.read_bytes()), 'mode': f.stat().st_mode
} for f in sorted(r.rglob('*')) if f.is_file()}
assert before == after
verification = {
    'status': 'MATCH', 'anchors': anchors,
    'read_only_verifier': result,
    'independent_complete_tree_canonical_blobs': len(auth),
    'canonical_bytes': canonical_bytes,
    'completed_original_whole_byte_comparisons': len(completed),
    'original_history_span_comparisons': len(load(m / 'history-reading.json')),
    'private_primary_whole_file_rechecks': len(primary),
    'copied_controls_observed_not_rerun': len(controls),
    'entire_completed_root_unchanged_files': len(after),
    'parent_semantically_read': [
        'REPORT.md', 'packet/FINAL.md', 'packet/NOTES.md', 'packet/PREFREEZE.md',
        'packet/verify_packet.py', 'packet/private/READING-ISOLATION.md',
    ],
    'parent_canonical_proof_read_claim': False,
    'verification_recovery': 'First run stopped on absent bytes in the visual-only primary metadata row; inspected exact metadata and used the disclosed PDF binding. No author mutation.',
    'mathematical_gate': False, 'count_change': 0,
}
(o / 'verification.json').write_text(json.dumps(verification, indent=2) + '\n')
print(json.dumps(verification, indent=2))
