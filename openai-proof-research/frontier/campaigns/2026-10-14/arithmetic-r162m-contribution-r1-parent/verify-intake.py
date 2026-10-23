#!/usr/bin/env python3
"""Read-only contribution packet and immutable-input checks; no math gate."""
from pathlib import Path
import hashlib
import json
import stat
import subprocess

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'arithmetic-r162m-contribution-r1-parent'
r = b / 'arithmetic-r162m-contribution-r1'
a = b / 'fresh-arithmetic-discovery-r162m'
m = r / 'packet/private'
sha = lambda d: hashlib.sha256(d).hexdigest()
load = lambda f: json.loads(f.read_bytes())
def snapshot(root):
    return {f.relative_to(root).as_posix(): {'bytes': f.stat().st_size,
        'mode': f.stat().st_mode, 'sha256': sha(f.read_bytes())}
        for f in root.rglob('*') if f.is_file()}
anchors = {
    'packet/FINAL.md': '3ef78dde0efbab9654034834fefae145b65413ec3c5608b051765ad6d6ce5c95',
    'MANIFEST.json': '1cfadc2b9df008254f19d9ac5310e550e4a2b7611c639d28fb33161c4a2a9d00',
    'REPORT.md': '9d5005f8b1ca5ee3782e9dd25e5a55c7a372d053032db602151e38f2cb9feac1'}
for rel, h in anchors.items():
    assert sha((r / rel).read_bytes()) == h
run = subprocess.run(['python', '-I', '-B', str(r / 'packet/verify_packet.py'),
    '--root', str(r), '--final-sha256', anchors['packet/FINAL.md'],
    '--manifest-sha256', anchors['MANIFEST.json'], '--report-sha256', anchors['REPORT.md']],
    check=True, capture_output=True, text=True)
v = json.loads(run.stdout)
assert v == {'artifact_check': 'matched', 'files': 69, 'mathematical_gate': 'not assigned'}
manifest = load(r / 'MANIFEST.json')
td = (p / 'sources/preprints-tree.json').read_bytes()
assert sha(td) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = json.loads(td)
assert len(tree['tree']) == 13223 and not tree['truncated']
lookup = {x['path']: x for x in tree['tree']}
auth = load(m / 'canonical-authentication.json')['files']
assert len(auth) == 29
for x in auth:
    d = (p / x['path']).read_bytes()
    y = lookup[x['upstream_path']]
    assert len(d) == x['bytes'] == y['size'] and sha(d) == x['sha256']
    assert x['git_blob'] == y['sha'] == hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
reading = load(m / 'canonical-reading.json')
by_path = {x['upstream_path']: x for x in auth}
text_bytes = 0
for x in reading:
    size = by_path[x['path']]['bytes']
    if not x['path'].endswith('.pdf'):
        end = 0
        for start, stop in sorted(x['extents']):
            assert start <= end and 0 <= start <= stop <= size
            end = max(end, stop)
        assert end == size
        text_bytes += size
assert text_bytes == 470177
history = load(m / 'original-reading.json')
assert len(history) == 5
for x in history:
    with (p / x['path']).open('rb') as f:
        f.seek(x['start']); d = f.read(x['end']-x['start'])
    assert sha(d) == x['span_sha256'] and d == (p / x['copy']).read_bytes()
members = [z for x in load(m / 'primary/acquisitions.json') for z in x['members']]
for x in members:
    d = (p / x['path']).read_bytes()
    assert len(d) == x['bytes'] and sha(d) == x['sha256']
pre, post = load(m / 'author-pre.json'), load(m / 'author-post.json')
assert pre == post and len(pre) == 21
for x in pre:
    f = p / x['path']
    assert f.stat().st_size == x['bytes'] and sha(f.read_bytes()) == x['sha256']
    assert oct(stat.S_IMODE(f.stat().st_mode)) == x['mode']
frozen = sha((a / 'packet/FROZEN-THEOREM.md').read_bytes())
proof = sha((a / 'packet/AUTHOR-PROOF.md').read_bytes())
assert frozen == '9b967d5563e22bd8b07283d34d574f5eed9d5e2dc696020835e4e12655d003e1'
assert proof == '6dd830369698429d2d3d713a07a11a895e68e52ee650e231ff7833219e58b3e3'
controls = load(m / 'ARTIFACT-CONTROLS.json')
assert len(controls) == 3 and controls[0]['result']['artifact_check'] == 'matched'
assert all('rejected' in x for x in controls[1:])
assert snapshot(a) == load(o / 'private/author-root-before.json')
assert snapshot(r) == load(o / 'private/review-root-before.json')
result = {'status': 'MATCH', 'anchors': anchors, 'read_only_verifier': v,
    'payload_files': len(manifest['files']), 'payload_bytes': sum(x['bytes'] for x in manifest['files']),
    'directories': len(manifest['directories']), 'canonical_blobs': 29,
    'reviewer_complete_non_pdf_reading_bytes_reported': text_bytes,
    'interval_metadata_is_not_semantic_reading': True, 'primary_member_bindings': len(members),
    'original_history_span_comparisons': 5, 'author_inputs_pre_post_current': 21,
    'frozen_sha256': frozen, 'proof_sha256': proof, 'saved_copied_controls_match': 3,
    'controls_rerun': False, 'review_root_unchanged_files': len(snapshot(r)),
    'author_root_unchanged_files': len(snapshot(a)),
    'parent_semantically_read': ['REPORT.md', 'packet/FINAL.md', 'packet/REVIEW.md',
        'packet/verify_packet.py', 'packet/private/COMPARISON.md', 'packet/private/READING-ISOLATION.md'],
    'parent_canonical_primary_proof_reread': False, 'transitive_reading_limits_retained': True,
    'parent_metadata_print_clipped': 'Overlarge canonical authentication print; recovered schema and fully parsed/verified all rows. No proof-body clipping.',
    'artifact_checks_assign_mathematical_gate': False, 'count_change': 0}
(o / 'verification.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
