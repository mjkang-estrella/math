#!/usr/bin/env python3
"""Read-only notified packet checks; reading records are not math gates."""
from pathlib import Path
import hashlib
import json
import subprocess

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'arithmetic-r162j-continuation-r1-parent'
r = b / 'arithmetic-r162j-continuation-r1'
m = r / 'packet/private'
sha = lambda data: hashlib.sha256(data).hexdigest()
load = lambda path: json.loads(path.read_bytes())
anchors = {
    'packet/FINAL.md': '5fb581450299fcdbdfaf431df96ad8711e661abc2ac10df617f5cc706bf09eb5',
    'packet/MANIFEST.json': 'fb44380a2b14a1252f3d64c333b428bdf744c6f146d0251fb8eaa87520c23ea8',
    'REPORT.md': '1bf5c370862be831faa4f3f2c98af6d8b0895540e2c18af085405c334dbe9030',
}
for rel, digest in anchors.items():
    assert sha((r / rel).read_bytes()) == digest
run = subprocess.run(['python', '-I', '-B', str(r / 'packet/VERIFY.py'),
    '--packet', str(r / 'packet'), '--report', str(r / 'REPORT.md'),
    '--final-sha256', anchors['packet/FINAL.md'],
    '--manifest-sha256', anchors['packet/MANIFEST.json'],
    '--report-sha256', anchors['REPORT.md']], check=True, capture_output=True, text=True)
verifier = json.loads(run.stdout)
assert verifier['files'] == 106 and verifier['writes'] == 0 and not verifier['mathematical_gate']
manifest = load(r / 'packet/MANIFEST.json')
tree_data = (p / 'sources/preprints-tree.json').read_bytes()
assert sha(tree_data) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = json.loads(tree_data)
assert len(tree['tree']) == 13223 and not tree['truncated']
by_path = {x['path']: x for x in tree['tree']}
auth = load(m / 'canonical-authentication.json')
assert len(auth) == 35
for e in auth:
    original = by_path[e['path']]
    assert all(e[k] == original[k] for k in ['path', 'mode', 'type', 'sha', 'size'])
    data = (r / e['local']).read_bytes()
    assert len(data) == e['size'] and sha(data) == e['sha256']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == e['sha']
reading = load(m / 'canonical-own-reading.json')
assert reading['non_pdf_bytes'] == 1019669
text_bytes = 0
for e in reading['files']:
    if e['path'].lower().endswith('.pdf'):
        continue
    end = 0
    for start, stop in sorted(e['own_display_extents']):
        assert 0 <= start <= end and start <= stop <= e['size']
        end = max(end, stop)
    assert end == e['size'] and not e['uncovered']
    text_bytes += e['size']
assert text_bytes == 1019669
history = load(m / 'history-reading.json')
for e in history:
    with (p / e['path']).open('rb') as f:
        f.seek(e['start']); data = f.read(e['end'] - e['start'])
    assert sha(data) == e['sha256']
    assert data == (m / e['local']).read_bytes()
primary = load(m / 'primary-own-reading.json')
for e in primary:
    data = (m / 'primary' / e['id'] / 'files' / e['file']).read_bytes()
    assert len(data) == e['size'] and sha(data) == e['sha256']
controls = load(m / 'controls/result.json')
assert controls['positive_copy_hash_equal'] and controls['altered_copy_hash_rejected']
assert not controls['mathematical_gate']
assert (m / 'controls/own-copy.txt').read_bytes() != (m / 'controls/own-copy-altered.txt').read_bytes()
after = {f.relative_to(r).as_posix(): {
    'bytes': f.stat().st_size, 'mode': f.stat().st_mode, 'sha256': sha(f.read_bytes())
} for f in r.rglob('*') if f.is_file()}
assert after == load(o / 'private/root-before.json')
result = {
    'status': 'MATCH', 'anchors': anchors, 'read_only_verifier': verifier,
    'payload_files': len(manifest['files']), 'payload_bytes': sum(x['size'] for x in manifest['files']),
    'canonical_blobs_against_complete_tree': len(auth), 'canonical_bytes': sum(x['size'] for x in auth),
    'author_non_pdf_own_reading_bytes_reported': text_bytes,
    'recorded_display_intervals_cover_all_non_pdf_text': True,
    'interval_or_hash_check_is_not_semantic_reading': True,
    'primary_file_binding_comparisons': len(primary), 'original_history_span_comparisons': len(history),
    'saved_copied_control_outcomes_match': True, 'copied_controls_rerun': False,
    'entire_completed_root_unchanged_files': len(after),
    'parent_semantically_read': ['REPORT.md', 'packet/FINAL.md', 'packet/PREFREEZE.md',
        'packet/VERIFY.py', 'packet/private/RESEARCH.md', 'packet/private/READING-ISOLATION.md'],
    'parent_canonical_primary_proof_reread': False,
    'canonical_reading_prerequisite_reported': 'COMPLETED; bounded primary/transitive limits retained',
    'mathematical_gate': False, 'count_change': 0,
}
(o / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
