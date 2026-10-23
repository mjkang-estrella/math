#!/usr/bin/env python3
"""Read-only child/direct-input checks, with receipts written only in this parent root."""
from pathlib import Path
import hashlib
import json
import runpy

P = Path(__file__).resolve().parents[4]
D = Path(__file__).resolve().parent
R = D.parent / 'fresh-arithmetic-discovery-r162aa'
def sha(b):
    return hashlib.sha256(b).hexdigest()
def snapshot(root):
    result = {}
    for p in root.rglob('*'):
        assert not p.is_symlink(), p
        if p.is_file():
            data = p.read_bytes()
            result[p.relative_to(root).as_posix()] = dict(bytes=len(data), mode=p.stat().st_mode, sha256=sha(data))
    return result

before = json.loads((D / 'private/intake/root-before.json').read_text())
assert snapshot(R) == before
anchors = dict(final='4ac6bb45f5ef808ff0692ca76b4102b11dc7911edafcebe2801b4a17f86255f4', manifest='941887cf435ba4723636fabf44fcea1d8ce1e24d5cb1371b96e9b957088b335b', report='3caa3c6ed20fd50e1d7a0fc0139a871656489617d927a97ec44cca1c8c1a09ee')
verify = runpy.run_path(str(R / 'verify_packet.py'))['verify']
count = verify(R, anchors['final'], anchors['manifest'], anchors['report'])
assert count == 65
tree_bytes = (P / 'sources/preprints-tree.json').read_bytes()
assert sha(tree_bytes) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree_json = json.loads(tree_bytes)
assert tree_json['truncated'] is False and len(tree_json['tree']) == 13223
tree = {x['path']: x for x in tree_json['tree']}
canonical = json.loads((R / 'packet/private/canonical-authentication.json').read_text())
assert len(canonical) == 27
for x in canonical:
    t = tree[x['path']]
    data = (R / 'packet/private/canonical' / x['path']).read_bytes()
    git_sha = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    assert len(data) == x['size'] == t['size']
    assert git_sha == x['git_blob'] == t['sha'] and sha(data) == x['sha256']
direct = json.loads((D / 'private/completed-direct-inputs.json').read_text())
assert len(direct) == 5
for x in direct:
    p = P / x['path']; data = p.read_bytes()
    assert len(data) == x['bytes'] and sha(data) == x['sha256'] and p.stat().st_mode == x['mode']
controls = json.loads((R / 'packet/private/copied-control-results.json').read_text())
assert [x.get('test') for x in controls[:5]] == ['copied baseline', 'changed copied own text', 'wrong detached manifest', 'wrong detached report', 'restored copied baseline']
assert controls[0]['accepted_entries'] == controls[4]['accepted_entries'] == 2
assert all('rejected' in x for x in controls[1:4])
assert snapshot(R) == before
manifest = json.loads((R / 'MANIFEST.json').read_text())
result = dict(status='MATCH', exact_manifest_files=count, manifest_bytes=sum(x['bytes'] for x in manifest['entries']), whole_root_files=len(before), whole_root_bytes_and_full_modes_unchanged=True, canonical_blobs=27, original_direct_inputs_unchanged=5, saved_control_outcomes_checked=5, saved_controls_not_rerun=True, detached_anchors=anchors, verifier_limits='Child verifier checks exact file membership and bytes; no directory or file-mode authentication is claimed for that verifier. Parent independently compares the entire 68-file root against its pre-read byte/full-mode snapshot.', parent_semantic_reading='FINAL, REPORT, full mathematical notebook, source/primary/history understanding and reading limits; original source/primary proofs not independently reread by parent.', mathematical_gate=False, count_change=0)
(D / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
