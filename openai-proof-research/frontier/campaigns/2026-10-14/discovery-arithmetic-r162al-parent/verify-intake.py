#!/usr/bin/env python3
"""Read-only exact selection verification, separate from mathematical gates."""
from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent
R=D.parent/'fresh-arithmetic-discovery-r162al'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def snapshot(root):
    result={}
    for f in root.rglob('*'):
        assert not f.is_symlink()
        if f.is_file():
            raw=f.read_bytes();result[f.relative_to(root).as_posix()]=dict(bytes=len(raw),sha256=sha(raw),mode=f.stat().st_mode)
    return result
before=json.loads((D/'private/intake/root-before.json').read_text())
assert len(before)==81 and snapshot(R)==before
anchors={'FINAL.md':'d85126803749b84a9daa2d58ea4e924c12a437b3ae687234446322d64dcbf669','private/MANIFEST.json':'5bde440cc44806b12030f9208cd934f571b3f426b573e674ba31978c980af185','REPORT.md':'24cf135be169ac8240fa324b89aff66e26e5f77e1b622df672b77c3dcc18c2cd'}
for n,h in anchors.items():assert sha((R/n).read_bytes())==h
m=json.loads((R/'private/MANIFEST.json').read_text());assert len(m['files'])==62
fixtures={n for n in before if n.startswith('private/integrity-controls/')}
assert len(fixtures)==17
assert set(before)=={x['path'] for x in m['files']}|{'private/MANIFEST.json','REPORT.md'}|fixtures
def command(root,a):return ['python','-I','-B',str(R/'verify.py'),str(root),'--final-sha256',a['FINAL.md'],'--manifest-sha256',a['private/MANIFEST.json'],'--report-sha256',a['REPORT.md']]
v=json.loads(subprocess.check_output(command(R,anchors),cwd=P,text=True));assert v['files']==62 and not v['mathematical_gate']
tree=json.loads((P/'sources/preprints-tree.json').read_text());by_path={x['path']:x for x in tree['tree']}
bindings=json.loads((R/'private/source/authentication.json').read_text());assert len(bindings)==30
for x in bindings:
    f=P/x['local'];assert f.is_relative_to(R/'private/source');raw=f.read_bytes();e=by_path[x['path']]
    assert len(raw)==x['bytes']==e['size'] and sha(raw)==x['sha256']
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==x['git_blob']==e['sha']
inputs=json.loads((D/'private/completed-direct-inputs.json').read_text());assert len(inputs)==5
for i,x in enumerate(inputs,1):
    f=P/x['path'];raw=f.read_bytes();assert len(raw)==x['bytes'] and sha(raw)==x['sha256'] and f.stat().st_mode==x['mode']
    assert (R/f'private/context/{i}.md').read_bytes()==raw
original=R/'private/integrity-controls/original'
fa={n:sha((original/n).read_bytes()) for n in anchors}
controls=[]
for name,ok in [('original',True),('changed-payload',False),('extra-file',False),('changed-report',False)]:
    result=subprocess.run(command(R/'private/integrity-controls'/name,fa),cwd=P,capture_output=True,text=True)
    assert (result.returncode==0)==ok
    controls.append(dict(fixture=name,accepted=result.returncode==0,as_expected=True))
assert snapshot(R)==before
out=dict(status='MATCH',manifest_files=62,manifest_bytes=sum(x['bytes'] for x in m['files']),whole_root_files=81,whole_root_bytes_and_full_modes_unchanged=True,exact_root_membership_checked=True,excluded_fixture_files=17,readonly_controls=controls,synthetic_mutations_not_rerun=True,canonical_text_git_bindings_checked=30,completed_direct_inputs_and_own_copies_unchanged=5,detached_anchors=anchors,parent_reading='Complete FINAL,REPORT,MATH,READING-LIMITS,WORKING and verifier;parent did not independently reread canonical/primary proofs.',limits='Child verifier checks62 selected bytes and exact membership outside17 fixture files plus detached REPORT/manifest;parent additionally checks exact81-file whole root and pre-read full modes,30 canonical Git bindings,5 original context copies and4 readonly copied controls. No directory-identity or mathematical gate follows.',artifact_check_only=True,correctness_gate=None,contribution_gate=None,count_change=0)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
