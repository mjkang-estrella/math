#!/usr/bin/env python3
"""Read-only nominee packet verification; no mathematical review or count."""
from pathlib import Path
import hashlib
import json
import subprocess

P=Path(__file__).resolve().parents[4]
D=Path(__file__).resolve().parent
R=D.parent/'fresh-arithmetic-discovery-r162aj'
def sha(b):return hashlib.sha256(b).hexdigest()
def snapshot():
    out={}
    for p in R.rglob('*'):
        assert not p.is_symlink()
        if p.is_file():
            raw=p.read_bytes();out[p.relative_to(R).as_posix()]=dict(bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw))
    return out
before=json.loads((D/'private/intake/root-before.json').read_text());assert len(before)==91 and snapshot()==before
anchors={'FINAL.md':'c42dae9543de949a2d52e8a2169ec3b86e3f783c1927cc10b4b82a7c2ecceb9f','MANIFEST.json':'1fe5f03cb525a0e555b507cc41369b156a7c70b8d8f769313bdc140b3638d9db','REPORT.md':'e6bf435f1708bf8e46f2381a94fc4e514acd0b8f27ca1b765a845f4ed1f67a2b'}
for n,h in anchors.items():assert sha((R/n).read_bytes())==h
check=subprocess.run(['python','-I','-B',str(R/'verify.py'),'--root',str(R),'--final',anchors['FINAL.md'],'--manifest',anchors['MANIFEST.json'],'--report',anchors['REPORT.md']],cwd=P,capture_output=True,text=True,check=True)
v=json.loads(check.stdout);assert v==dict(verified=True,files=81,read_only=True,mathematical_gate=False)
m=json.loads((R/'MANIFEST.json').read_text());assert len(m['files'])==81 and sum(x['bytes'] for x in m['files'])==7158871
extras={'ANCHORS.json','FINAL.md','MANIFEST.json','REPORT.md','verify.py','controls/copied-tiny/FINAL.md','controls/copied-tiny/MANIFEST.json','controls/copied-tiny/REPORT.md','controls/copied-tiny/packet/probe.txt','controls/copied-tiny/verify.py'}
assert set(before)=={x['path'] for x in m['files']}|extras
assert sha((R/'packet/STATEMENT.md').read_bytes())=='6a73b45333ee99648324171a070cec4fab8613a7af9b8687f87db7d0d31721e4'
assert sha((R/'packet/AUTHOR-PROOF.md').read_bytes())=='7980d626908175daf46c3326860a10888f26b61a252379e941b34636585a3817'
raw=(P/'sources/preprints-tree.json').read_bytes();assert sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(raw);assert len(tree['tree'])==13223 and not tree['truncated'];tree={x['path']:x for x in tree['tree']}
auth=json.loads((R/'packet/private/source-authentication.json').read_text());assert len(auth)==52
for x in auth:
    p=R/'packet/private/upstream'/x['path'];assert p.resolve().is_relative_to(R.resolve());raw=p.read_bytes();t=tree[x['path']]
    assert len(raw)==x['bytes']==t['size'] and sha(raw)==x['sha256']
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==x['git_blob']==t['sha']
direct=json.loads((D/'private/completed-direct-inputs.json').read_text());assert len(direct)==5
for x in direct:
    p=P/x['path'];raw=p.read_bytes();assert len(raw)==x['bytes'] and sha(raw)==x['sha256'] and p.stat().st_mode==x['mode']
c=json.loads((R/'packet/private/integrity-controls.json').read_text())
assert c['original_statement_unchanged'] and [x['control'] for x in c['controls']]==['valid fresh copied fixture','modified copied payload','unlisted copied payload','wrong explicit FINAL anchor','restored copied fixture']
assert all(x.get('accepted',x.get('rejected')) is True for x in c['controls'])
assert snapshot()==before
result=dict(status='MATCH',exact_manifest_files=81,manifest_bytes=7158871,whole_root_files=91,whole_root_bytes_and_full_modes_unchanged=True,parent_exact_root_membership_checked=True,canonical_blobs_independently_bound=52,completed_direct_inputs_unchanged=5,saved_control_outcomes_checked=5,synthetic_mutations_not_rerun=True,detached_anchors=anchors,frozen_statement_sha256='6a73b45333ee99648324171a070cec4fab8613a7af9b8687f87db7d0d31721e4',author_proof_sha256='7980d626908175daf46c3326860a10888f26b61a252379e941b34636585a3817',verifier_limits='Child checks exact packet bytes,verifier digest and3 anchors,not root extras,modes,directory identities,mathematics or provenance. Parent adds exact91-file root membership/pre-read bytes/full modes,52 complete-tree Git bindings and5 unchanged admitted originals.',parent_reading='Complete statement,author proof,comparison,prefreeze research,handoff and reading records/limits. Initial bundled proof display clipped; complete author proof reread untruncated. Original source/primary proofs not independently reread by parent.',mathematical_gate=False,count_change=0)
(D/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
