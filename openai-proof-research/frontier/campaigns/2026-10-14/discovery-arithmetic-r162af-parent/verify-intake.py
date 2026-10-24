#!/usr/bin/env python3
"""Read-only completed-packet verification; no mathematical gate."""
from pathlib import Path
import hashlib
import json
import runpy

P=Path(__file__).resolve().parents[4]
D=Path(__file__).resolve().parent
R=D.parent/'fresh-arithmetic-discovery-r162af'
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
anchors={'FINAL.md':'314a3d57e865048e9e7325600a39f61dc01f0861dabd01d3ff276a28fca7d250','MANIFEST.json':'43fecc0f2882b7ca8dd7b7c282968c71a86a942a1e627e2d68666500febb9e0e','REPORT.md':'ced2c3f0be6d402868be8adaa7998a8ef969e97d92aab721799a1561d17d9df7'}
v=runpy.run_path(str(R/'verify.py'))['verify'](R,anchors['FINAL.md'],anchors['MANIFEST.json'],anchors['REPORT.md'])
assert v['files']==51 and v['bytes']==3036995 and v['mathematical_gate'] is False
raw_tree=(P/'sources/preprints-tree.json').read_bytes()
assert sha(raw_tree)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(raw_tree);assert len(tree['tree'])==13223 and tree['truncated'] is False
tree={x['path']:x for x in tree['tree']}
auth=json.loads((R/'packet/private/canonical-authentication.json').read_text());assert len(auth)==13
for x in auth:
    p=R/x['local'];assert p.resolve().is_relative_to(R.resolve())
    raw=p.read_bytes();t=tree[x['path']];blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
    assert len(raw)==x['size']==t['size'] and blob==x['git_blob']==t['sha'] and sha(raw)==x['sha256']
direct=json.loads((D/'private/completed-direct-inputs.json').read_text());assert len(direct)==5
for x in direct:
    p=P/x['path'];raw=p.read_bytes();assert len(raw)==x['bytes'] and sha(raw)==x['sha256'] and p.stat().st_mode==x['mode']
controls=json.loads((R/'packet/private/copied-controls/outcomes.json').read_text())
assert controls['copied_bytes']==180 and controls['mathematical_gate'] is False
assert controls['source_sha256_unchanged']==sha((R/controls['source']).read_bytes())
cases=controls['results']
assert [x['case'] for x in cases]==['intact','body-byte','extra-file','missing-file','final-anchor','manifest-anchor','report-anchor','unsafe-path']
assert [x['observed'] for x in cases]==['accept','reject','reject','reject','reject','reject','reject','reject'] and all(x['expected']==x['observed'] for x in cases)
assert snapshot()==before
result=dict(status='MATCH',exact_manifest_files=51,manifest_bytes=3036995,whole_root_files=len(before),whole_root_bytes_and_full_modes_unchanged=True,canonical_blobs=13,original_direct_inputs_unchanged=5,saved_control_outcomes_checked=8,saved_controls_not_rerun=True,detached_anchors=anchors,verifier_limits='Child verifier checks file bytes and selected membership,not directory identities,modes or canonical bindings to the complete tree. Parent independently verifies all13 bindings and compares all54 root files against pre-read bytes/full modes.',parent_reading='Complete handoff,full provisional scope,notebook,source/primary/history understanding and limits; original source/primary proofs not independently reread by parent.',mathematical_gate=False,count_change=0)
(D/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
