#!/usr/bin/env python3
"""Read-only correctness-review artifact and immutable-input checks."""
from pathlib import Path
import hashlib
import json
import stat
import subprocess

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'arithmetic-r162m-proof-r1-parent'
r = b / 'arithmetic-r162m-proof-r1'
a = b / 'fresh-arithmetic-discovery-r162m'
m = r / 'packet/private'
sha = lambda d: hashlib.sha256(d).hexdigest()
load = lambda f: json.loads(f.read_bytes())

def snapshot(root):
    return {f.relative_to(root).as_posix(): {'bytes': f.stat().st_size,
        'mode': f.stat().st_mode, 'sha256': sha(f.read_bytes())}
        for f in root.rglob('*') if f.is_file()}

anchors = {
    'packet/FINAL.md': '240943b5a112814dddd9bacd15703b09dca213e343327f5412a7a9603d84fca1',
    'MANIFEST.json': 'b9b12f5712d75381cd0d99e7e1eb94ea6a3786a12f6de7f7165bee859cafe9c6',
    'REPORT.md': '45b1509edcfe9d6c6dcb6aeef8c7d342bb955dd3acad2df734f1b5e34fe856c7',
}
for rel, digest in anchors.items():
    assert sha((r / rel).read_bytes()) == digest
run = subprocess.run(['python', '-I', '-B', str(r / 'packet/verify_packet.py'), str(r),
    '--final-sha256', anchors['packet/FINAL.md'], '--manifest-sha256', anchors['MANIFEST.json'],
    '--report-sha256', anchors['REPORT.md']], check=True, capture_output=True, text=True)
verifier = json.loads(run.stdout)
assert verifier['files'] == 67 and verifier['directories'] == 20
assert not verifier['mathematical_gate_assigned']
manifest = load(r / 'MANIFEST.json')
entries = [x for x in manifest['entries'] if x['type'] == 'file']
tree_data = (p / 'sources/preprints-tree.json').read_bytes()
assert sha(tree_data) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = json.loads(tree_data)
assert len(tree['tree']) == 13223 and not tree['truncated']
by_path = {x['path']: x for x in tree['tree']}
auth = load(m / 'canonical-authentication.json')
assert len(auth) == 29
for e in auth:
    original = by_path[e['path']]
    data = (m / 'canonical' / e['path']).read_bytes()
    assert original['size'] == e['bytes'] == len(data)
    assert original['sha'] == e['git_blob'] and sha(data) == e['sha256']
    assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == e['git_blob']
own = load(m / 'own-reading.json')
canonical_text, primary_count, history_count = 0, 0, 0
for e in own:
    if e['kind'] == 'original-history':
        assert len(e['semantic_extents']) == 1
        start, end = e['semantic_extents'][0]
        with (p / e['path']).open('rb') as f:
            f.seek(start); data = f.read(end - start)
        assert len(data) == e['span_bytes'] and sha(data) == e['span_sha256']
        assert data == (m / e['copy']).read_bytes()
        history_count += 1
    else:
        data = (m / e['path']).read_bytes()
        assert len(data) == e['bytes'] and sha(data) == e['sha256']
        if e['kind'] == 'primary':
            primary_count += 1
        elif not e['path'].endswith('.pdf'):
            assert e['complete_text_read']
            end = 0
            for start, stop in sorted(e['semantic_extents']):
                assert start <= end and 0 <= start <= stop <= len(data)
                end = max(end, stop)
            assert end == len(data)
            canonical_text += len(data)
pre, post = load(m / 'author-pre.json'), load(m / 'author-post.json')
assert pre == post and len(pre) == 21
for e in pre:
    f = p / e['path']
    assert f.stat().st_size == e['bytes'] and sha(f.read_bytes()) == e['sha256']
    assert oct(stat.S_IMODE(f.stat().st_mode)) == e['mode']
frozen_sha = sha((a / 'packet/FROZEN-THEOREM.md').read_bytes())
proof_sha = sha((a / 'packet/AUTHOR-PROOF.md').read_bytes())
assert frozen_sha == '9b967d5563e22bd8b07283d34d574f5eed9d5e2dc696020835e4e12655d003e1'
assert proof_sha == '6dd830369698429d2d3d713a07a11a895e68e52ee650e231ff7833219e58b3e3'
controls = load(m / 'controls-result.json')
assert controls['intact'] == 'OK' and controls['changed_copied_text'] == 'rejected'
assert controls['wrong_detached_anchor'] == 'rejected' and controls['verifier_is_read_only']
assert not controls['mathematical_gate_assigned']
assert snapshot(r) == load(o / 'private/review-root-before.json')
assert snapshot(a) == load(o / 'private/author-root-before.json')
result = {'status': 'MATCH', 'anchors': anchors, 'read_only_verifier': verifier,
    'payload_files': len(entries), 'payload_bytes': sum(x['bytes'] for x in entries),
    'canonical_blobs_against_complete_tree': 29, 'reviewer_complete_non_pdf_reading_bytes_reported': canonical_text,
    'interval_metadata_is_not_semantic_reading': True, 'primary_file_bindings': primary_count,
    'original_history_span_comparisons': history_count, 'immutable_author_inputs_pre_post_current': 21,
    'frozen_sha256': frozen_sha, 'proof_sha256': proof_sha, 'saved_copied_controls_match': 3,
    'controls_rerun': False, 'review_root_unchanged_files': len(snapshot(r)),
    'author_root_unchanged_files': len(snapshot(a)),
    'parent_semantically_read': ['REPORT.md', 'packet/FINAL.md', 'packet/REVIEW.md',
        'packet/verify_packet.py', 'packet/private/READING-AND-APPLICATIONS.md'],
    'parent_canonical_primary_proof_reread': False, 'transitive_reading_limits_retained': True,
    'artifact_checks_assign_mathematical_gate': False, 'other_review_not_queried': True,
    'count_change': 0}
(o / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
