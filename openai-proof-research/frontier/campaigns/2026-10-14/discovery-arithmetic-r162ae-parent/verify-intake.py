#!/usr/bin/env python3
"""Read-only verification of completed r162ae and admitted completed originals."""
from pathlib import Path
import hashlib
import json
import runpy

P=Path(__file__).resolve().parents[4]
D=Path(__file__).resolve().parent
R=D.parent/'fresh-arithmetic-discovery-r162ae'
def sha(raw):
    return hashlib.sha256(raw).hexdigest()
def snapshot():
    result={}
    for p in R.rglob('*'):
        assert not p.is_symlink()
        if p.is_file():
            raw=p.read_bytes();result[p.relative_to(R).as_posix()]=dict(bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw))
    return result
before=json.loads((D/'private/intake/root-before.json').read_text())
assert snapshot()==before
anchors={'FINAL.md':'95f39248c9e868b2ae85ff922839e9aada4f2241fcef353ae252af3dd0736445','MANIFEST.json':'7fe51505026adf5057ed1003986f4ea827427ad296d87895bbf6554837595f4a','REPORT.md':'80599601fb0dbaeef86f81d804f65c7b037496c8e8acf451bd2efd6c13572bae'}
verified=runpy.run_path(str(R/'verify.py'))['verify'](R,anchors)
assert verified['selected_files']==78 and verified['selected_bytes']==5043230 and verified['canonical_blobs']==35
raw_tree=(P/'sources/preprints-tree.json').read_bytes()
assert sha(raw_tree)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(raw_tree);assert len(tree['tree'])==13223 and tree['truncated'] is False
tree={x['path']:x for x in tree['tree']}
auth=json.loads((R/'packet/private/canonical-authentication.json').read_text());assert len(auth)==35
for x in auth:
    p=R/'packet/private/canonical'/x['path'];assert p.resolve().is_relative_to(R.resolve())
    raw=p.read_bytes();t=tree[x['path']];blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
    assert len(raw)==x['bytes']==t['size'] and blob==x['git_blob']==t['sha'] and sha(raw)==x['sha256']
direct=json.loads((D/'private/completed-direct-inputs.json').read_text());assert len(direct)==5
for x in direct:
    p=P/x['path'];raw=p.read_bytes();assert len(raw)==x['bytes'] and sha(raw)==x['sha256'] and p.stat().st_mode==x['mode']
cases=json.loads((R/'packet/private/controls/outcomes.json').read_text())['cases']
assert [x['case'] for x in cases]==['unchanged copied own text','modified copied note','extra copied file','wrong explicit FINAL anchor','wrong explicit MANIFEST anchor','wrong explicit REPORT anchor','restored copied own text']
assert [x['accepted'] for x in cases]==[True,False,False,False,False,False,True] and all(x['accepted']==x['expected'] for x in cases)
assert snapshot()==before
result=dict(status='MATCH',exact_manifest_files=78,manifest_bytes=5043230,whole_root_files=len(before),whole_root_bytes_and_full_modes_unchanged=True,canonical_blobs=35,original_direct_inputs_unchanged=5,saved_control_outcomes_checked=7,saved_controls_not_rerun=True,detached_anchors=anchors,verifier_limits='Child verifier checks file bytes,membership and35 canonical bindings,not directory identities or modes. Parent separately compares all81 root files against pre-read bytes/full modes and the complete canonical tree.',parent_reading='Complete handoff,full provisional scope,notebook,source/primary/history understanding and reading limits; original source/primary proofs not independently reread by parent.',mathematical_gate=False,count_change=0)
(D/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
