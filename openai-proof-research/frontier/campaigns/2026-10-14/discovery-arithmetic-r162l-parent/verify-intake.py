#!/usr/bin/env python3
"""Read-only artifact/input verification; no mathematical gates."""
from pathlib import Path
import hashlib
import json
import subprocess

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'discovery-arithmetic-r162l-parent'
r = b / 'fresh-arithmetic-discovery-r162l'
m = r / 'packet/private'
sha = lambda d: hashlib.sha256(d).hexdigest()
load = lambda f: json.loads(f.read_bytes())
anchors = {
    'packet/FINAL.md': '832013613b8a41b64260e9e124afef3e1c4b0dd8e801c0e466319f47257f46e9',
    'private/MANIFEST.json': '9dcc78f74df6a54ede8428808a626165061fc71ae2684a7c783f04d0c1ffe04a',
    'REPORT.md': '58dd36a77b2c534c2b987672a8a7ddccd8c419ba9ef61e1a3c32c3286f3ae72b',
}
for rel, digest in anchors.items():
    assert sha((r / rel).read_bytes()) == digest
run = subprocess.run(['python', '-I', '-B', str(r / 'packet/verify_packet.py'),
    '--packet', str(r / 'packet'), '--manifest', str(r / 'private/MANIFEST.json'),
    '--report', str(r / 'REPORT.md'), '--final-sha256', anchors['packet/FINAL.md'],
    '--manifest-sha256', anchors['private/MANIFEST.json'],
    '--report-sha256', anchors['REPORT.md']], check=True, capture_output=True, text=True)
verifier = json.loads(run.stdout)
assert verifier['files'] == 76 and not verifier['mathematical_gate']
manifest = load(r / 'private/MANIFEST.json')
tree_data = (p / 'sources/preprints-tree.json').read_bytes()
assert sha(tree_data) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = json.loads(tree_data)
assert len(tree['tree']) == 13223 and not tree['truncated']
by_path = {x['path']: x for x in tree['tree']}
auth = load(m / 'canonical-authentication.json')
assert len(auth) == 35
for e in auth:
    original = by_path[e['path']]
    data = (p / e['local']).read_bytes()
    assert original['size'] == e['size'] == len(data)
    assert original['sha'] == e['git_blob'] and sha(data) == e['sha256']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == e['git_blob']
reading = load(m / 'canonical-reading.json')
assert len(reading) == 32
text_bytes = 0
for e in reading:
    size = by_path[e['path']]['size']
    assert e['extent'] == [0, size] and e['complete_semantic_read']
    text_bytes += size
history = load(m / 'history-reading.json')
for e in history:
    with (p / e['path']).open('rb') as f:
        f.seek(e['start']); data = f.read(e['end'] - e['start'])
    assert sha(data) == e['sha256'] and data == (p / e['local']).read_bytes()
primary = load(m / 'primary-reading.json')
for e in primary:
    data = (m / 'primary' / e['file']).read_bytes()
    assert len(data) == e['bytes'] and sha(data) == e['sha256']
exceptions = ['discovery-arithmetic-r162k-parent/assessment.md',
    'fresh-arithmetic-discovery-r162k/packet/FINAL.md',
    'fresh-arithmetic-discovery-r162k/packet/private/RESEARCH.md',
    'fresh-arithmetic-discovery-r162k/packet/private/READING-ISOLATION.md']
for i, rel in enumerate(exceptions):
    assert (b / rel).read_bytes() == (m / ('completed-' + str(i) + '.txt')).read_bytes()
controls = load(m / 'copied-controls/RESULTS.json')
assert controls['original_unchanged'] and controls['copied_final_restored']
assert len(controls['controls']) == 3
assert all(x['returncode'] == x['expected_returncode'] for x in controls['controls'])
after = {f.relative_to(r).as_posix(): {
    'bytes': f.stat().st_size, 'mode': f.stat().st_mode, 'sha256': sha(f.read_bytes())
} for f in r.rglob('*') if f.is_file()}
assert after == load(o / 'private/root-before.json')
result = {'status': 'MATCH', 'anchors': anchors, 'read_only_verifier': verifier,
    'payload_files': len(manifest['files']), 'payload_bytes': sum(x['bytes'] for x in manifest['files']),
    'canonical_blobs_against_complete_tree': 35, 'canonical_bytes': sum(x['size'] for x in auth),
    'author_complete_non_pdf_reading_objects_reported': 32,
    'author_complete_non_pdf_reading_bytes_reported': text_bytes,
    'reading_metadata_does_not_prove_semantic_reading': True,
    'original_history_span_comparisons': len(history), 'completed_original_whole_comparisons': 4,
    'primary_file_binding_comparisons': len(primary), 'saved_copied_controls_match': 3,
    'controls_rerun': False, 'entire_completed_root_unchanged_files': len(after),
    'parent_semantically_read': ['REPORT.md', 'packet/FINAL.md', 'packet/verify_packet.py',
        'packet/private/PREFREEZE-CALCULATIONS.md', 'packet/private/READING-ISOLATION.md'],
    'parent_canonical_primary_proof_reread': False,
    'full_transitive_primary_reading': 'NOT_ATTAINED; inaccessible original packing proof and unread dependencies disclosed',
    'mathematical_gate': False, 'count_change': 0}
(o / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
