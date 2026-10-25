#!/usr/bin/env python3
"""Parent read-only authentication of the frozen author packet, not a math gate."""
from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;R=D.parent/'fresh-arithmetic-discovery-r162bc'
def sha(a):return hashlib.sha256(a).hexdigest()
def pairs(xs):
 assert len({k for k,v in xs})==len(xs),'duplicate JSON key'
 return dict(xs)
def read(p):return json.loads(p.read_bytes(),object_pairs_hook=pairs)
def snap(root):
 out={}
 for f in root.rglob('*'):
  assert not f.is_symlink()
  if f.is_file():
   a=f.read_bytes();assert stat.S_ISREG(f.stat().st_mode) and f.stat().st_nlink==1
   out[f.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=f.stat().st_mode)
 return out
anchors={'private/FINAL.md':'77c0db0923db412d1a850b4313f3cf7f813eabe0708fe8578924cea7dccee1ad','private/MANIFEST.json':'13fc541ab1ef5bc71761d9e83bef83c7675669d1790fd422739d3933db8e0938','REPORT.md':'4f4f2ebaa8c0e356a491c95d9e9e2229cc58caec2f19a63ae482d246659edb89'}
before=read(D/'private/intake/root-before.json');assert snap(R)==before
for n,h in anchors.items():assert sha((R/n).read_bytes())==h
cmd=['python','-I','-B',str(R/'private/verify.py'),'--root',str(R),'--final',anchors['private/FINAL.md'],'--manifest',anchors['private/MANIFEST.json'],'--report',anchors['REPORT.md']]
run=subprocess.run(cmd,cwd=P,capture_output=True,text=True);assert run.returncode==0,run.stderr
result=json.loads(run.stdout);assert result['artifact_check']=='PASS' and result['payload_files']==63 and result['whole_root_files']==66 and result['subdirectories']==11
m=read(R/'private/MANIFEST.json');fp=[e['path'] for e in m['files']];dp=[e['path'] for e in m['directories']]
assert fp==sorted(fp) and len(fp)==len(set(fp)) and dp==sorted(dp) and len(dp)==len(set(dp))
assert len({s.casefold() for s in fp+dp+list(anchors)})==len(fp)+len(dp)+3
for s in fp+dp:
 z=PurePosixPath(s);assert s and '\\' not in s and '\0' not in s and not z.is_absolute() and str(z)==s and all(t not in {'.','..'} for t in s.split('/'))
assert set(before)==set(fp)|set(anchors)
assert {f.relative_to(R).as_posix() for f in R.rglob('*') if f.is_dir()}==set(dp)
assert stat.S_IMODE(R.stat().st_mode)==m['root_mode']
for e in m['files']:
 f=R/e['path'];a=f.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and stat.S_IMODE(f.stat().st_mode)==e['mode']
for e in m['directories']:assert stat.S_IMODE((R/e['path']).stat().st_mode)==e['mode']
treebytes=(P/'sources/preprints-tree.json').read_bytes();assert sha(treebytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(treebytes);assert not tree['truncated'];tb={e['path']:e for e in tree['tree']}
selected=read(R/'private/source-tree.json');bindings=read(R/'private/source-bindings.json')
assert len(selected)==16 and len(bindings)==12 and len({e['path'] for e in selected})==16
for e in selected:
 z=tb[e['path']];assert all(e[k]==z[k] for k in ['path','mode','type','sha'])
 if e['type']=='blob':assert e['size']==z['size']
assert {e['path'] for e in bindings}=={e['path'] for e in selected if e['type']=='blob'}
for e in bindings:
 a=(R/e['local']).read_bytes();assert len(a)==e['size'] and sha(a)==e['sha256'] and hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['sha']
inputs=read(D/'private/completed-direct-inputs.json');ib={e['path']:e for e in inputs};copies=read(R/'private/copies.json');assert len(inputs)==5 and len(copies)==6
for e in copies:
 a=(R/e['local']).read_bytes();assert len(a)==e['bytes'] and sha(a)==e['original_sha256']
 if e['original'] in ib:
  z=ib[e['original']];f=P/e['original'];assert a==f.read_bytes() and len(a)==z['bytes'] and sha(a)==z['sha256'] and f.stat().st_mode==z['mode']
 else:
  assert e['original']=='sources/CONTENTS.md binary [223610,225119)'
  with (P/'sources/CONTENTS.md').open('rb') as f:f.seek(223610);assert f.read(1509)==a
frozen=read(R/'private/freeze.json');statement=(R/'private/STATEMENT.md').read_bytes();proof=(R/'private/PROOF.md').read_bytes()
assert len(statement)==2250==frozen['bytes'] and sha(statement)==frozen['sha256']=='ffb70a869024e8ebf88964edb0a41575d2d3922976579e93dd593a2d4ed3f528'
assert sha(proof)=='dc51e6cc034a28da0f229bae81f85a00eee98be03d3dc9afe26521165f055fca'
ns={'__name__':'parent_readonly_authentication'};exec(compile((R/'private/verify.py').read_text(),str(R/'private/verify.py'),'exec'),ns)
wrong=[]
for n in anchors:
 a=dict(anchors);a[n]='0'*64
 try:ns['verify'](R,a)
 except AssertionError as e:assert 'detached anchor mismatch' in str(e);wrong.append(str(e))
 else:raise AssertionError('wrong detached anchor accepted')
fixture=R/'private/controls/fixture';fixture_result=ns['verify'](fixture,{n:sha((fixture/n).read_bytes()) for n in anchors})
controls=read(R/'private/artifact-controls.json');assert len(controls)==9 and all(e['observed_accept']==e['expected_accept'] for e in controls)
assert snap(R)==before
v=dict(status='MATCH',artifact_only=True,bundled_verifier_passed=True,bundled_verifier=dict(returncode=run.returncode,stdout=run.stdout,stderr=run.stderr,sha256=sha((R/'private/verify.py').read_bytes())),independent_membership_hash_length_mode_check=True,payload_files=63,payload_bytes=sum(e['bytes'] for e in m['files']),whole_root_files=66,subdirectories=11,canonical_blobs=12,canonical_entries=16,completed_originals_and_copies=5,catalogue_bounded_copy=True,statement_sha256=sha(statement),statement_bytes=len(statement),proof_sha256=sha(proof),proof_bytes=len(proof),anchors=anchors,author_copied_control_receipts=controls,intact_fixture_readonly_recheck=fixture_result,wrong_anchor_controls=wrong,all_completed_original_bytes_and_full_modes_unchanged=True,whole_root_bytes_and_full_modes_unchanged=True,mathematical_gates_assigned=False)
(D/'verification.json').write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n');print(json.dumps({k:v[k] for k in ['status','payload_files','payload_bytes','whole_root_files','subdirectories','canonical_blobs','statement_sha256','proof_sha256','whole_root_bytes_and_full_modes_unchanged']}))
