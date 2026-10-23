#!/usr/bin/env python3
"""Verify a frozen nominee's packet and bindings; assign no mathematical gate."""
from pathlib import Path
import hashlib
import json
import subprocess

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'arithmetic-r162m-nominee-parent'
r = b / 'fresh-arithmetic-discovery-r162m'
packet, m = r / 'packet', r / 'packet/private'
sha = lambda d: hashlib.sha256(d).hexdigest()
load = lambda f: json.loads(f.read_bytes())
anchors = {
    'packet/FINAL.md': '392e4da2db6bf09d8909bfc617076f74d0276857a86aa276ce1a24bdd669fe5e',
    'MANIFEST.json': 'e60d17ab380041e6276a3b1c9849e5e5d5c4b33c9f8fcedba9e31df280b511c5',
    'REPORT.md': '6ecd286c9a85c25529297378d7f8f4cffc9531e0da1cbbd78159bcf9a5ed85ba',
}
for rel, digest in anchors.items():
    assert sha((r / rel).read_bytes()) == digest
run = subprocess.run(['python', '-I', '-B', str(packet / 'verify_packet.py'), '--root', str(r),
    '--final-sha256', anchors['packet/FINAL.md'], '--manifest-sha256', anchors['MANIFEST.json'],
    '--report-sha256', anchors['REPORT.md']], check=True, capture_output=True, text=True)
manifest = load(r / 'MANIFEST.json')
assert len(manifest['files']) == 96
tree_data = (p / 'sources/preprints-tree.json').read_bytes()
assert sha(tree_data) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = json.loads(tree_data)
assert len(tree['tree']) == 13223 and not tree['truncated']
by_path = {x['path']: x for x in tree['tree']}
auth = load(m / 'canonical-authentication.json')
assert len(auth) == 29
for e in auth:
    original = by_path[e['path']]
    data = (packet / e['local']).read_bytes()
    assert original['size'] == e['bytes'] == len(data)
    assert original['sha'] == e['git_blob'] and sha(data) == e['sha256']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == e['git_blob']
reading = load(m / 'canonical-reading.json')
text_bytes = 0
for e in reading:
    if e['path'].endswith('.pdf'):
        continue
    size = by_path[e['path']]['size']
    assert e['extent'] == [0, size] and e['mode'] == 'full semantic text read'
    text_bytes += size
assert len([e for e in reading if not e['path'].endswith('.pdf')]) == 27
originals = load(m / 'original-reading.json')
for e in originals:
    original = (p / e['path']).read_bytes()
    assert sha(original) == e['sha256'] and len(original) == e['bytes']
    data = original[e['start']:e['end']]
    assert data == (packet / e['copy']).read_bytes()
primary = load(m / 'primary-reading.json')
for e in primary:
    data = (packet / e['path']).read_bytes()
    assert len(data) == e['bytes'] and sha(data) == e['sha256']
for e in load(m / 'completed-exceptions.json'):
    assert sha((p / e['path']).read_bytes()) == e['sha256']
frozen, proof = (packet / 'FROZEN-THEOREM.md').read_bytes(), (packet / 'AUTHOR-PROOF.md').read_bytes()
freeze = load(m / 'FREEZE-RECEIPT.json')
assert sha(frozen) == freeze['sha256'] == '9b967d5563e22bd8b07283d34d574f5eed9d5e2dc696020835e4e12655d003e1'
assert len(frozen) == freeze['bytes'] == 1645
assert sha(proof) == '6dd830369698429d2d3d713a07a11a895e68e52ee650e231ff7833219e58b3e3'
controls = load(m / 'ARTIFACT-CONTROLS.json')['results']
assert len(controls) == 7
assert controls[0]['exit_code'] == 0 and all(x['exit_code'] == 1 for x in controls[1:])
assert all(x['read_only_snapshot_equal'] for x in controls)
after = {f.relative_to(r).as_posix(): {
    'bytes': f.stat().st_size, 'mode': f.stat().st_mode, 'sha256': sha(f.read_bytes())
} for f in r.rglob('*') if f.is_file()}
assert after == load(o / 'private/root-before.json')
result = {'status': 'MATCH', 'anchors': anchors, 'read_only_verifier_stdout': run.stdout,
    'payload_files': len(manifest['files']), 'payload_bytes': sum(x['bytes'] for x in manifest['files']),
    'frozen_sha256': sha(frozen), 'frozen_bytes': len(frozen), 'proof_sha256': sha(proof), 'proof_bytes': len(proof),
    'author_freeze_chronology_receipt_retained_not_independently_certified': True,
    'canonical_blobs_against_complete_tree': 29, 'canonical_bytes': sum(x['bytes'] for x in auth),
    'author_complete_non_pdf_reading_objects_reported': 27,
    'author_complete_non_pdf_reading_bytes_reported': text_bytes,
    'reading_metadata_is_not_semantic_reading': True, 'primary_file_binding_comparisons': len(primary),
    'original_history_span_comparisons': len(originals), 'completed_original_hash_comparisons': 4,
    'saved_copied_controls_match': 7, 'controls_rerun': False,
    'entire_author_root_unchanged_files': len(after),
    'parent_semantically_read': ['REPORT.md', 'packet/FINAL.md', 'packet/FROZEN-THEOREM.md',
        'packet/AUTHOR-PROOF.md', 'packet/verify_packet.py', 'packet/private/SOURCE-INTERFACE.md',
        'packet/private/READING-ISOLATION.md', 'packet/private/PREFREEZE-CALCULATIONS.md', 'packet/private/AUTHOR-CHECK.md'],
    'parent_canonical_primary_proof_reread': False, 'transitive_primary_gaps_retained': True,
    'verification_recovery': 'Original-history bytes/hash fields bind whole originals, while start/end bind semantic spans. Initial check stopped on that distinction; whole-original hashes and exact copied spans now checked separately. Author files unchanged.',
    'correctness_gate': None, 'contribution_gate': None, 'accepted': False, 'count_change': 0}
(o / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
