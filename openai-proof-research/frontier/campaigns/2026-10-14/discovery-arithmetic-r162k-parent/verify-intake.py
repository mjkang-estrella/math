#!/usr/bin/env python3
"""Read-only packet and input checks; no mathematical gate."""
from pathlib import Path
import hashlib
import json
import subprocess

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'discovery-arithmetic-r162k-parent'
r = b / 'fresh-arithmetic-discovery-r162k'
m = r / 'packet/private'
sha = lambda d: hashlib.sha256(d).hexdigest()
load = lambda f: json.loads(f.read_bytes())
anchors = {
    'packet/FINAL.md': 'fbd67ca66206e6652009644387a4dd784bcc3149ba3e38d6908e98fa1d9074be',
    'packet/MANIFEST.json': 'c63b83649deef8905c5600589ed7c916ae40ccbd4e314e6f5dcce1a74961b41b',
    'REPORT.md': 'ed309247e51456e4e91720a700c283ef514b7e6fe24399a8f1ff18794e0da5de',
}
for rel, digest in anchors.items():
    assert sha((r / rel).read_bytes()) == digest
run = subprocess.run(['python', '-I', '-B', str(r / 'packet/verify_packet.py'),
    '--packet', str(r / 'packet'), '--report', str(r / 'REPORT.md'),
    '--final-sha256', anchors['packet/FINAL.md'],
    '--manifest-sha256', anchors['packet/MANIFEST.json'],
    '--report-sha256', anchors['REPORT.md']], check=True, capture_output=True, text=True)
verifier = json.loads(run.stdout)
assert verifier['members'] == 57 and not verifier['mathematical_gate']
manifest = load(r / 'packet/MANIFEST.json')
tree_data = (p / 'sources/preprints-tree.json').read_bytes()
assert sha(tree_data) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = json.loads(tree_data)
assert len(tree['tree']) == 13223 and not tree['truncated']
by_path = {x['path']: x for x in tree['tree']}
auth = load(m / 'canonical-authentication.json')
assert len(auth) == 17
for e in auth:
    original = by_path[e['path']]
    data = (m / e['local']).read_bytes()
    assert original['size'] == e['size'] == len(data)
    assert original['sha'] == e['git_blob']
    assert sha(data) == e['sha256']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == e['git_blob']
reading = load(m / 'canonical-reading.json')['full_non_pdf_reads']
assert len(reading) == 16
text_bytes = 0
for e in reading:
    data = (m / e['local']).read_bytes()
    assert e['raw_bytes_read'] == [0, len(data)] and e['semantic_read'] == 'complete'
    assert sha(data) == e['sha256']
    text_bytes += len(data)
assert text_bytes == 257892
history = load(m / 'history-reading.json')
for e in history:
    with (p / e['original']).open('rb') as f:
        f.seek(e['extent'][0]); data = f.read(e['extent'][1] - e['extent'][0])
    assert sha(data) == e['sha256'] and data == (m / e['local']).read_bytes()
primary_count = 0
for e in load(m / 'primary-authentication.json'):
    assert sha((m / ('primary-' + e['id'] + '.tar')).read_bytes()) == e['sha256']
    for f in e['files']:
        data = (m / ('primary-' + e['id']) / f['path']).read_bytes()
        assert len(data) == f['size'] and sha(data) == f['sha256']
        primary_count += 1
hu = load(m / 'primary-hu-authentication.json')
data = (m / 'primary-hu-2020.pdf').read_bytes()
assert len(data) == hu['bytes'] and sha(data) == hu['sha256']
exceptions = [
    ('arithmetic-r162j-continuation-r1-parent/assessment.md', 'exception-assessment.md'),
    ('arithmetic-r162j-continuation-r1/packet/FINAL.md', 'exception-FINAL.md'),
    ('arithmetic-r162j-continuation-r1/packet/private/RESEARCH.md', 'exception-RESEARCH.md'),
    ('arithmetic-r162j-continuation-r1/packet/private/READING-ISOLATION.md', 'exception-READING-ISOLATION.md'),
]
for original, copied in exceptions:
    assert (b / original).read_bytes() == (m / copied).read_bytes()
controls = load(m / 'ARTIFACT-CONTROLS.json')
assert len(controls['cases']) == 3 and not controls['originals_mutated']
assert all(x['accepted'] == x['expected'] for x in controls['cases'])
after = {f.relative_to(r).as_posix(): {
    'bytes': f.stat().st_size, 'mode': f.stat().st_mode, 'sha256': sha(f.read_bytes())
} for f in r.rglob('*') if f.is_file()}
assert after == load(o / 'private/root-before.json')
result = {'status': 'MATCH', 'anchors': anchors, 'read_only_verifier': verifier,
    'payload_members': len(manifest['files']), 'payload_bytes': sum(x['bytes'] for x in manifest['files']),
    'canonical_blobs_against_complete_tree': 17, 'canonical_bytes': sum(x['size'] for x in auth),
    'author_complete_non_pdf_reading_bytes_reported': text_bytes,
    'reading_metadata_does_not_prove_semantic_reading': True,
    'original_history_span_comparisons': len(history), 'completed_original_whole_comparisons': 4,
    'primary_archive_bindings': 4, 'extracted_primary_bindings': primary_count,
    'published_primary_pdf_binding': 1, 'saved_copied_controls_match': 3, 'controls_rerun': False,
    'entire_completed_root_unchanged_files': len(after),
    'parent_semantically_read': ['REPORT.md', 'packet/FINAL.md', 'packet/verify_packet.py',
        'packet/private/RESEARCH.md', 'packet/private/READING-ISOLATION.md'],
    'parent_canonical_primary_proof_reread': False, 'primary_transitive_limits_preserved': True,
    'mathematical_gate': False, 'count_change': 0}
(o / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
