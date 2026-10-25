#!/usr/bin/env python3
"""Read-only parent authentication, preserving the bundled ordering defect."""
from pathlib import Path, PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
R=B/'fresh-arithmetic-discovery-r162bb'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def snap(root):
 out={}
 for f in root.rglob('*'):
  assert not f.is_symlink()
  if f.is_file():
   a=f.read_bytes();out[f.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=f.stat().st_mode)
 return out
anchors={'private/FINAL.md':'4f74631ff3471efdcca58855381cf0391d95b2972b289ff7ca7159124beaa6f9','private/MANIFEST.json':'ecf38cc08ca303b1366d147a717d63de6b974965015afa4b21f54d29c71c3cb8','REPORT.md':'2b330a3b04dee749acf3a61d6d5249b8bbcd5fd1756c01f01d97b6e4ffb7d808'}
before=json.loads((D/'private/intake/root-before.json').read_text());assert snap(R)==before
for n,h in anchors.items():assert sha((R/n).read_bytes())==h
cmd=['python','-I','-B',str(R/'verify.py'),'--root',str(R),'--final-sha256',anchors['private/FINAL.md'],'--manifest-sha256',anchors['private/MANIFEST.json'],'--report-sha256',anchors['REPORT.md']]
original=subprocess.run(cmd,cwd=P,capture_output=True,text=True)
assert original.returncode!=0 and 'file records not sorted unique' in original.stderr
m=json.loads((R/'private/MANIFEST.json').read_bytes());records=m['files'];dirs=m['directories']
fp=[e['path'] for e in records];dp=[e['path'] for e in dirs]
assert fp!=sorted(fp) and len(fp)==len(set(fp)) and dp==sorted(dp) and len(dp)==len(set(dp))
assert len({s.casefold() for s in fp+dp+list(anchors)})==len(fp)+len(dp)+3
for s in fp+dp:
 p=PurePosixPath(s);assert s and '\\' not in s and '\0' not in s and not p.is_absolute() and str(p)==s and all(t not in {'.','..'} for t in p.parts)
assert set(before)==set(fp)|set(anchors)
assert {f.relative_to(R).as_posix() for f in R.rglob('*') if f.is_dir()}==set(dp)
assert stat.S_IMODE(R.stat().st_mode)==m['root_mode']
for e in records:
 f=R/e['path'];a=f.read_bytes();assert f.stat().st_nlink==1 and stat.S_ISREG(f.stat().st_mode)
 assert len(a)==e['bytes'] and sha(a)==e['sha256'] and stat.S_IMODE(f.stat().st_mode)==e['mode']
for e in dirs:assert stat.S_IMODE((R/e['path']).stat().st_mode)==e['mode']
for n in anchors:assert stat.S_IMODE((R/n).stat().st_mode)==(0o644 if n=='REPORT.md' else 0o600)
tree_bytes=(P/'sources/preprints-tree.json').read_bytes();assert sha(tree_bytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tree_bytes);assert not tree['truncated'];tb={e['path']:e for e in tree['tree']}
meta=json.loads((R/'private/selected-metadata.json').read_text());auth=json.loads((R/'private/authentication.json').read_text())
assert len(meta)==55 and len(auth)==43 and len({e['path'] for e in meta})==55 and len({e['path'] for e in auth})==43
for e in meta:
 z=tb[e['path']];assert all(e[k]==z[k] for k in ['path','mode','type','sha'])
 if e['type']=='blob':assert e['size']==z['size']
mb={e['path']:e for e in meta if e['type']=='blob'};assert set(mb)=={e['path'] for e in auth}
for e in auth:
 a=(R/'private/source'/e['path']).read_bytes();z=mb[e['path']]
 assert len(a)==z['size']==e['size'] and sha(a)==e['sha256'] and hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==z['sha']==e['sha']
copies=json.loads((R/'private/exception-copies.json').read_text());inputs=json.loads((D/'private/completed-direct-inputs.json').read_text());assert len(copies)==len(inputs)==5
ib={e['path']:e for e in inputs};assert set(ib)=={e['original'] for e in copies}
for e in copies:
 z=ib[e['original']];f=P/e['original'];a=f.read_bytes();c=(R/e['copy']).read_bytes()
 assert a==c and len(a)==e['length']==z['bytes'] and sha(a)==e['sha256']==z['sha256'] and f.stat().st_mode==e['mode']==z['mode']
src=(R/'verify.py').read_text();old="need(fp==sorted(fp) and len(fp)==len(set(fp)),'file records not sorted unique')";new="need(len(fp)==len(set(fp)),'file records not unique')"
assert src.count(old)==1
ns={'__name__':'parent_readonly_verifier'};exec(compile(src.replace(old,new),str(R/'verify.py'),'exec'),ns)
corrected=ns['verify'](R,list(anchors.values()));assert corrected['payload_files']==78 and corrected['whole_root_files']==81 and corrected['subdirectories']==21
wrong=[]
for i in range(3):
 a=list(anchors.values());a[i]='0'*64
 try:ns['verify'](R,a)
 except ValueError as exc:assert 'detached anchor mismatch' in str(exc);wrong.append(str(exc))
 else:raise AssertionError('wrong anchor accepted')
fixture=R/'private/controls/fixture';fh=[sha((fixture/n).read_bytes()) for n in anchors]
fixture_result=ns['verify'](fixture,fh)
controls=json.loads((R/'private/controls/results.json').read_text());assert len(controls['tests'])==7 and all((e['observed']=='accepted')==e['expected_accept'] for e in controls['tests'])
assert snap(R)==before
v=dict(status='MATCH_WITH_BUNDLED_VERIFIER_DEFECT',artifact_only=True,bundled_verifier_passed=False,bundled_verifier=dict(returncode=original.returncode,stdout=original.stdout,stderr=original.stderr,sha256=sha(src.encode())),defect='Unique manifest file records are unsorted; bundled ordering assertion rejects them.',in_memory_correction=dict(original_line=old,replacement_line=new,only_ordering_requirement_relaxed=True,sealed_files_changed=False,result=corrected),independent_exact_membership_hash_length_mode_check=True,payload_files=78,payload_bytes=sum(e['bytes'] for e in records),whole_root_files=81,subdirectories=21,canonical_blobs=43,canonical_entries=55,completed_originals_and_copies=5,all_completed_original_bytes_and_full_modes_unchanged=True,anchors=anchors,wrong_anchor_controls=wrong,existing_fixture_readonly_recheck=fixture_result,author_copied_control_receipts=controls,whole_root_bytes_and_full_modes_unchanged=True,mathematical_gates_assigned=False)
dump(D/'verification.json',v);print(json.dumps({k:v[k] for k in ['status','payload_files','payload_bytes','whole_root_files','subdirectories','canonical_blobs','completed_originals_and_copies','bundled_verifier_passed','whole_root_bytes_and_full_modes_unchanged']}))
