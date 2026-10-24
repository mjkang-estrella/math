#!/usr/bin/env python3
"""Read-only verification of the completed child and exact admitted originals."""
from pathlib import Path
import hashlib
import json
import runpy

P=Path(__file__).resolve().parents[4]
D=Path(__file__).resolve().parent
R=D.parent/'fresh-arithmetic-discovery-r162ad'
def sha(raw):
    return hashlib.sha256(raw).hexdigest()
def snapshot():
    result={}
    for p in R.rglob('*'):
        assert not p.is_symlink()
        if p.is_file():
            raw=p.read_bytes()
            result[p.relative_to(R).as_posix()]=dict(bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw))
    return result
before=json.loads((D/'private/intake/root-before.json').read_text())
assert snapshot()==before
anchors={'FINAL.md':'c6ce45bb2671ce7891782070a6ca51c17dc363bb07e220f5923a4aabfd7d4f4a','MANIFEST.json':'029f7eaba94287ad9c53310887b47c61d4e729c5f21f3285c7b114b16bcb2748','REPORT.md':'6015a739a2a0c47e52cc58a8972386dd1f4441cffd0cbca1d84f0bb31d1ec3f5'}
verified=runpy.run_path(str(R/'verify.py'))['verify'](R,anchors)
assert verified['files']==46 and verified['bytes']==4605798 and verified['canonical_bindings']==11 and verified['writes']==0
raw_tree=(P/'sources/preprints-tree.json').read_bytes()
assert sha(raw_tree)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(raw_tree)
assert len(tree['tree'])==13223 and tree['truncated'] is False
tree={x['path']:x for x in tree['tree']}
auth=json.loads((R/'packet/private/authentication.json').read_text())
assert len(auth)==11
for x in auth:
    p=R/x['local'];assert p.resolve().is_relative_to(R.resolve())
    raw=p.read_bytes();t=tree[x['path']]
    blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
    assert len(raw)==x['size']==t['size'] and blob==x['git_blob']==t['sha'] and sha(raw)==x['sha256']
direct=json.loads((D/'private/completed-direct-inputs.json').read_text())
assert len(direct)==5
for x in direct:
    p=P/x['path'];raw=p.read_bytes()
    assert len(raw)==x['bytes'] and sha(raw)==x['sha256'] and p.stat().st_mode==x['mode']
controls=json.loads((R/'packet/private/controls/outcomes.json').read_text())['cases']
assert [x['case'] for x in controls]==['unaltered tiny own fixture','copied member mutation','extra copied member','missing copied member','wrong explicit report anchor','restored tiny own fixture']
assert [x['exit_code'] for x in controls]==[0,1,1,1,1,0]
assert all(x['read_only'] and x['expected_accept']==(x['exit_code']==0) for x in controls)
rules=(R/'packet/private/prospective-isolation.json').read_text()
assert '*arithmetic*162ad*' in rules and '*arithmetic*r162ad*' in rules
assert snapshot()==before
result=dict(status='MATCH',exact_manifest_files=46,manifest_bytes=4605798,whole_root_files=len(before),whole_root_bytes_and_full_modes_unchanged=True,canonical_blobs=11,original_direct_inputs_unchanged=5,saved_control_outcomes_checked=6,saved_controls_not_rerun=True,detached_anchors=anchors,child_serialized_r_and_no_r_twins_present=True,timing_limit='Child reports both twins preceded its sole optional traversal; parent does not infer timing from artifact hashes alone.',verifier_limits='Child verifier authenticates file bytes,membership and11 canonical bindings,not directory identities or modes. Parent separately compares the entire49-file root against pre-read bytes/full modes.',parent_reading='Complete handoff,notebook,source/primary/history understanding,reading limits and process correction; original source/primary proofs not independently reread by parent.',mathematical_gate=False,count_change=0)
(D/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
