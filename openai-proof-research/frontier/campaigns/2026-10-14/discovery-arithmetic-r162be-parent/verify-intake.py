#!/usr/bin/env python3
"""Read-only authentication of an author packet; no mathematical gate from bytes."""
from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent;R=B/'fresh-arithmetic-discovery-r162be'
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
anchors={'FINAL.md':'2129f37c0849b61cf6eba5aa55d0d6b7bd4406c71b6b0bd09ff76305b71a02ba','MANIFEST.json':'67e701201139eee1b5755f99b9c7c55a47be879ea3fdd40d23b8f758b88b9597','REPORT.md':'04cef8ff60eb67aa045d702cc39e8fbd3fd4b56f912eb8ac3feb410d268a3a81'}
before=read(D/'private/intake/root-before.json');assert snap(R)==before
for n,h in anchors.items():assert sha((R/n).read_bytes())==h
cmd=['python','-I','-B',str(R/'VERIFY.py'),'--final',anchors['FINAL.md'],'--manifest',anchors['MANIFEST.json'],'--report',anchors['REPORT.md']]
run=subprocess.run(cmd,cwd=P,capture_output=True,text=True);assert run.returncode==0,run.stderr;result=json.loads(run.stdout)
assert result['artifact_integrity']=='MATCH' and result['payload_records']==44 and result['whole_root_files']==46 and result['directories_including_root']==11 and result['source_blobs']==10 and result['exact_completed_copies']==5
m=read(R/'MANIFEST.json');fp=[e['path'] for e in m['files']];dp=[e['path'] for e in m['directories']]
assert fp==sorted(fp) and len(fp)==len(set(fp)) and dp==sorted(dp) and len(dp)==len(set(dp))
assert 'FINAL.md' in fp and m['envelopes']==['MANIFEST.json','REPORT.md'] and set(before)==set(fp)|set(m['envelopes'])
assert len({n.casefold() for n in before})==46
for n in fp+dp:
 if n=='.':assert n in dp;continue
 z=PurePosixPath(n);assert n and '\\' not in n and '\0' not in n and not z.is_absolute() and str(z)==n and all(x not in {'.','..',''} for x in n.split('/'))
actual_dirs={'.':stat.S_IMODE(R.stat().st_mode),**{f.relative_to(R).as_posix():stat.S_IMODE(f.stat().st_mode) for f in R.rglob('*') if f.is_dir()}}
assert m['directories']==[dict(path=n,mode=actual_dirs[n]) for n in sorted(actual_dirs)]
for e in m['files']:
 f=R/e['path'];a=f.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and stat.S_IMODE(f.stat().st_mode)==e['mode']
for n,mode in m['envelope_modes'].items():assert stat.S_IMODE((R/n).stat().st_mode)==mode
tree_bytes=(P/'sources/preprints-tree.json').read_bytes();assert sha(tree_bytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tree_bytes);assert not tree['truncated'];tb={e['path']:e for e in tree['tree']}
meta=read(R/'private/source/tree-selection.json');auth=read(R/'private/source/authentication.json');assert len(meta)==15 and len(auth)==10 and len({e['path'] for e in meta})==15
prefix='preprints/Simulating-One-Tape-Time-in-Two-Fifths-Power-Space-September-25-2026'
for e in meta:
 z=tb[e['path']];assert all(e[k]==z[k] for k in ['path','mode','type','sha'])
 if e['type']=='blob':assert e['size']==z['size']
assert {e['path'] for e in auth}=={e['path'] for e in meta if e['type']=='blob'}
for e in auth:
 rel=e['path'][len(prefix)+1:];a=(R/'private/source'/rel).read_bytes();z=tb[e['path']]
 assert len(a)==e['bytes']==z['size'] and sha(a)==e['sha256'] and hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['git_blob']==z['sha']
copies=read(R/'private/COPY-BINDINGS.json');inputs=read(D/'private/completed-direct-inputs.json');ib={e['path']:e for e in inputs}
assert len(copies)==len(inputs)==5 and {e['original'] for e in copies}==set(ib)
for e in copies:
 z=ib[e['original']];f=P/e['original'];a=f.read_bytes();c=R/e['copy']
 assert a==c.read_bytes() and len(a)==e['bytes']==z['bytes'] and sha(a)==e['sha256']==z['sha256']
 assert f.stat().st_mode==z['mode'] and stat.S_IMODE(f.stat().st_mode)==e['original_mode'] and stat.S_IMODE(c.stat().st_mode)==e['copy_mode']
ns={'__name__':'parent_readonly_packet_authentication','__file__':str(R/'VERIFY.py')};exec(compile((R/'VERIFY.py').read_text(),str(R/'VERIFY.py'),'exec'),ns)
wrong=[]
for n in anchors:
 a=dict(anchors);a[n]='0'*64
 try:ns['verify'](R,a['FINAL.md'],a['MANIFEST.json'],a['REPORT.md'])
 except AssertionError as exc:assert 'detached anchor' in str(exc);wrong.append(dict(anchor=n,rejected=str(exc)))
 else:raise AssertionError('wrong anchor accepted')
control=R/'private/controls/FINAL.copy';a=control.read_bytes();assert a==(R/'FINAL.md').read_bytes()
rec=dict(path='private/controls/FINAL.copy',bytes=len(a),sha256=sha(a),mode=stat.S_IMODE(control.stat().st_mode));ns['check_file'](R,rec)
try:ns['check_file'](R,dict(rec,mode=rec['mode']^0o100))
except AssertionError as exc:assert ': mode' in str(exc);mode_rejected=str(exc)
else:raise AssertionError('wrong expected mode accepted')
controls=read(R/'private/controls/RESULTS.json');assert snap(R)==before
v=dict(status='MATCH',artifact_only=True,bundled_verifier_passed=True,bundled_verifier=dict(returncode=run.returncode,stdout=run.stdout,stderr=run.stderr,sha256=sha((R/'VERIFY.py').read_bytes())),independent_exact_membership_hash_length_mode_check=True,payload_records=44,payload_records_include_final=True,payload_bytes=sum(e['bytes'] for e in m['files']),whole_root_files=46,directories_including_root=11,canonical_blobs=10,canonical_entries=15,completed_originals_and_copies=5,original_mode_bindings_recorded_by_author_at_late_comparison=True,parent_initial_full_modes_also_matched=True,all_completed_original_bytes_and_full_modes_unchanged=True,anchors=anchors,derivations_sha256=sha((R/'private/DERIVATIONS.md').read_bytes()),reading_limits_sha256=sha((R/'private/READING-LIMITS.md').read_bytes()),author_copied_control_receipts=controls,intact_final_copy_readonly_check=True,wrong_expected_mode_rejected=mode_rejected,wrong_anchor_controls=wrong,whole_root_bytes_and_full_modes_unchanged=True,mathematical_gates_assigned=False)
(D/'verification.json').write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n');print(json.dumps({k:v[k] for k in ['status','payload_records','payload_bytes','whole_root_files','directories_including_root','canonical_blobs','completed_originals_and_copies','whole_root_bytes_and_full_modes_unchanged']}))
