#!/usr/bin/env python3
"""Read-only exact-packet,canonical-binding and unchanged-original comparisons."""
from pathlib import Path
import hashlib
import json
import runpy

P=Path(__file__).resolve().parents[4]
D=Path(__file__).resolve().parent
R=D.parent/'fresh-arithmetic-discovery-r162ai'
def sha(b):return hashlib.sha256(b).hexdigest()
def snapshot():
    out={}
    for p in R.rglob('*'):
        assert not p.is_symlink()
        if p.is_file():
            raw=p.read_bytes();out[p.relative_to(R).as_posix()]=dict(bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw))
    return out
before=json.loads((D/'private/intake/root-before.json').read_text());assert len(before)==60 and snapshot()==before
anchors={'FINAL.md':'f5d830a114689b32a7908f3e3b969799117709c03c02fbc3d8a3297c5141196a','MANIFEST.json':'0dcc818fc79ef66ecb6b187090b0acd5977ac658a67ab90fd5c92c6e44f51dba','REPORT.md':'b92bf951d006da0670406a4d80dfc0bbfc13bde154eb7575f0b3fb6f9f6b5f63'}
verified=runpy.run_path(str(R/'packet/public/verify_packet.py'))['verify'](R,anchors);assert verified==57
m=json.loads((R/'MANIFEST.json').read_text());assert sum(x['bytes'] for x in m['files'])==6015430
assert set(before)=={x['path'] for x in m['files']}|set(anchors)
raw=(P/'sources/preprints-tree.json').read_bytes();assert sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(raw);assert len(tree['tree'])==13223 and not tree['truncated'];tree={x['path']:x for x in tree['tree']}
auth=json.loads((R/'packet/private/authentication.json').read_text());assert len(auth)==20
for x in auth:
    p=P/x['local'];assert p.resolve().is_relative_to(R.resolve());raw=p.read_bytes();t=tree[x['path']]
    assert len(raw)==x['bytes']==t['size'] and sha(raw)==x['sha256']
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==x['git_blob']==t['sha']
direct=json.loads((D/'private/completed-direct-inputs.json').read_text());assert len(direct)==5
for x in direct:
    p=P/x['path'];raw=p.read_bytes();assert len(raw)==x['bytes'] and sha(raw)==x['sha256'] and p.stat().st_mode==x['mode']
c=json.loads((R/'packet/private/integrity-controls/control-results.json').read_text())
assert c['baseline']==1 and c['baseline_unchanged'] is True and c['payload_rejected']=='packet content mismatch: packet/value.txt' and c['anchor_rejected']=='detached anchor mismatch: FINAL.md'
assert snapshot()==before
v=dict(status='MATCH',exact_manifest_files=57,manifest_bytes=6015430,whole_root_files=60,whole_root_bytes_and_full_modes_unchanged=True,parent_exact_root_membership_checked=True,canonical_blobs_independently_bound=20,completed_direct_inputs_unchanged=5,saved_control_outcomes_checked=3,synthetic_mutations_not_rerun=True,detached_anchors=anchors,verifier_limits='Child verifies three anchors and exact packet bytes,not modes,directory identities,root extras,mathematics or provenance. Parent adds exact60-file root membership/pre-read bytes/full modes,20 complete-tree Git bindings and5 readonly-original comparisons.',parent_reading='Complete handoff,scope,research,reading limits/records and saved check outcomes; combined research display clipping recovered by full sections5-6 reread. Original source/primary proofs not independently reread by parent.',mathematical_gate=False,count_change=0)
(D/'verification.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v))
