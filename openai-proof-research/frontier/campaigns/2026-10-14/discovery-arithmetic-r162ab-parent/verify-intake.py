#!/usr/bin/env python3
"""Read-only detached-anchor intake; receipts stay in this parent's root."""
from pathlib import Path
import hashlib
import json
import runpy

P = Path(__file__).resolve().parents[4]
D = Path(__file__).resolve().parent
R = D.parent / 'fresh-arithmetic-discovery-r162ab'
def sha(data):
    return hashlib.sha256(data).hexdigest()
def snapshot():
    result = {}
    for p in R.rglob('*'):
        assert not p.is_symlink()
        if p.is_file():
            data = p.read_bytes()
            result[p.relative_to(R).as_posix()] = dict(bytes=len(data), mode=p.stat().st_mode, sha256=sha(data))
    return result
before = json.loads((D / 'private/intake/root-before.json').read_text())
assert snapshot() == before
anchors = dict(final='5a7781bf94299854bf1c9f8995737a7d30d5ebde4f85da7d37e884891ae478fa', manifest='4b738139ad488acd0d611adb9182764390339a9b9eee0fbda594f8914e909f7d', report='dfa5aab48616568fc2e3141698ebf82f6970d25340d738a1123a96cf4e6be89d')
count = runpy.run_path(str(R / 'verify.py'))['verify'](R, anchors['final'], anchors['manifest'], anchors['report'])
assert count == 48
raw_tree = (P / 'sources/preprints-tree.json').read_bytes()
assert sha(raw_tree) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree = json.loads(raw_tree)
assert len(tree['tree']) == 13223 and tree['truncated'] is False
tree = {x['path']: x for x in tree['tree']}
canonical = json.loads((R / 'packet/private/canonical-authentication.json').read_text())
assert len(canonical) == 13
for x in canonical:
    local = P / x['local']
    assert local.resolve().is_relative_to(R.resolve())
    data = local.read_bytes(); t = tree[x['path']]
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    assert len(data) == x['bytes'] == t['size'] and blob == x['git_blob'] == t['sha'] and sha(data) == x['sha256']
direct = json.loads((D / 'private/completed-direct-inputs.json').read_text())
assert len(direct) == 5
for x in direct:
    p = P / x['path']; data = p.read_bytes()
    assert len(data) == x['bytes'] and p.stat().st_mode == x['mode'] and sha(data) == x['sha256']
controls = json.loads((R / 'packet/private/copied-controls-results.json').read_text())
assert [x['control'] for x in controls] == ['untouched copied text','changed copied text','extra copied file','wrong detached report anchor','restored copied fixture']
assert [x['exit'] for x in controls] == [0,1,1,1,0]
assert [x['expected'] for x in controls] == [True,False,False,False,True]
assert snapshot() == before
manifest = json.loads((R / 'MANIFEST.json').read_text())
result = dict(status='MATCH', exact_manifest_files=count, manifest_bytes=sum(x['bytes'] for x in manifest['files']), whole_root_files=len(before), whole_root_bytes_and_full_modes_unchanged=True, canonical_blobs=13, original_direct_inputs_unchanged=5, saved_control_outcomes_checked=5, saved_controls_not_rerun=True, detached_anchors=anchors, verifier_limits='Child verifier checks selected file membership and bytes, not directory identities or modes. Parent separately compares all 51 root files against its pre-read byte/full-mode snapshot.', parent_reading='Complete FINAL, REPORT, notebook, source/primary/history understanding and reading limits; source/primary original proofs not independently reread by parent.', mathematical_gate=False, count_change=0)
(D / 'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
