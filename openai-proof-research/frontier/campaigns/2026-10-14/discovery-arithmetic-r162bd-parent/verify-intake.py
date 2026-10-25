#!/usr/bin/env python3
"""Read-only parent authentication, independent of mathematical findings."""
from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent;R=B/'fresh-arithmetic-discovery-r162bd'
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
anchors={'FINAL.md':'b1669c81b09e16780e2c23612da06aa76a9982f7eeb529a68e347ef204143d78','MANIFEST.json':'d23b7427e6bb992163ab844572ea5d794c99ba14c91675531e0444494ba8e8ad','REPORT.md':'2c10188d95779de1b074ebfc94cd24505beb050c7e15e71b336b486bb39bd877'}
before=read(D/'private/intake/root-before.json');assert snap(R)==before
for n,h in anchors.items():assert sha((R/n).read_bytes())==h
cmd=['python','-I','-B',str(R/'VERIFY.py'),'--root',str(R),'--final-sha256',anchors['FINAL.md'],'--manifest-sha256',anchors['MANIFEST.json'],'--report-sha256',anchors['REPORT.md']]
run=subprocess.run(cmd,cwd=P,capture_output=True,text=True);assert run.returncode==0,run.stderr;result=json.loads(run.stdout)
assert result['artifact_verification']=='PASS' and result['payload_files']==55 and result['whole_root_files']==57 and result['directories_including_root']==7 and result['source_and_copy_bindings']
m=read(R/'MANIFEST.json');fp=[e['path'] for e in m['files']];dp=[e['path'] for e in m['directories']]
assert fp==sorted(fp) and len(fp)==len(set(fp)) and dp==sorted(dp) and len(dp)==len(set(dp))
assert 'FINAL.md' in fp and 'REPORT.md' not in fp and 'MANIFEST.json' not in fp
assert set(before)==set(fp)|{'MANIFEST.json','REPORT.md'} and len({n.casefold() for n in before})==57
for n in fp+dp:
 if n=='':assert n in dp;continue
 z=PurePosixPath(n);assert n and '\\' not in n and '\0' not in n and not z.is_absolute() and str(z)==n and all(x not in {'.','..',''} for x in n.split('/'))
actual_dirs={'':stat.S_IMODE(R.stat().st_mode),**{f.relative_to(R).as_posix():stat.S_IMODE(f.stat().st_mode) for f in R.rglob('*') if f.is_dir()}}
assert m['directories']==[dict(path=n,mode=actual_dirs[n]) for n in sorted(actual_dirs)]
for e in m['files']:
 f=R/e['path'];a=f.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and stat.S_IMODE(f.stat().st_mode)==e['mode']
for n,mode in m['envelope_modes'].items():assert stat.S_IMODE((R/n).stat().st_mode)==mode
tree_bytes=(P/'sources/preprints-tree.json').read_bytes();assert sha(tree_bytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tree_bytes);assert not tree['truncated'];tb={e['path']:e for e in tree['tree']}
meta=read(R/'private/source-metadata.json');auth=read(R/'private/source-authentication.json');assert len(meta)==19 and len(auth)==16 and len({e['path'] for e in meta})==19
for e in meta:
 z=tb[e['path']];assert all(e[k]==z[k] for k in ['path','mode','type','sha'])
 if e['type']=='blob':assert e['size']==z['size']
assert {e['path'] for e in auth}=={e['path'] for e in meta if e['type']=='blob'}
for e in auth:
 f=P/e['local'];assert f.is_relative_to(R);a=f.read_bytes();z=tb[e['path']]
 assert len(a)==e['bytes']==z['size'] and sha(a)==e['sha256'] and hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['git_blob']==z['sha']
copies=read(R/'private/COPY-BINDINGS.json');inputs=read(D/'private/completed-direct-inputs.json');ib={e['path']:e for e in inputs};assert copies['compared_before_seal'] and len(copies['copies'])==len(inputs)==5
assert {e['original'] for e in copies['copies']}==set(ib)
for e in copies['copies']:
 z=ib[e['original']];f=P/e['original'];a=f.read_bytes();c=R/e['local']
 assert a==c.read_bytes() and len(a)==e['bytes']==z['bytes'] and sha(a)==e['sha256']==z['sha256']
 assert f.stat().st_mode==z['mode'] and stat.S_IMODE(f.stat().st_mode)==e['original_mode'] and stat.S_IMODE(c.stat().st_mode)==e['copy_mode']
ns={'__name__':'parent_readonly_packet_authentication'};exec(compile((R/'VERIFY.py').read_text(),str(R/'VERIFY.py'),'exec'),ns)
wrong=[]
for n in anchors:
 a=dict(anchors);a[n]='0'*64
 try:ns['verify'](R,a)
 except ValueError as exc:assert 'anchor mismatch' in str(exc);wrong.append(dict(anchor=n,rejected=str(exc)))
 else:raise AssertionError('wrong anchor accepted')
controls=read(R/'private/ARTIFACT-CONTROLS.json');fixture=R/'private/copied-control';fixture_result=ns['verify'](fixture,controls['fixture_anchors'])
assert fixture_result==controls['restored_copy']==controls['valid_copy'] and controls['originals_unchanged']
assert snap(R)==before
v=dict(status='MATCH',artifact_only=True,bundled_verifier_passed=True,bundled_verifier=dict(returncode=run.returncode,stdout=run.stdout,stderr=run.stderr,sha256=sha((R/'VERIFY.py').read_bytes())),independent_exact_membership_hash_length_mode_check=True,payload_files=55,payload_records_include_final=True,payload_bytes=sum(e['bytes'] for e in m['files']),whole_root_files=57,directories_including_root=7,canonical_blobs=16,canonical_entries=19,completed_originals_and_copies=5,all_completed_original_bytes_and_full_modes_unchanged=True,anchors=anchors,derivations_sha256=sha((R/'private/DERIVATIONS.md').read_bytes()),reading_limits_sha256=sha((R/'private/READING-LIMITS.md').read_bytes()),author_copied_control_receipts=controls,intact_fixture_readonly_recheck=fixture_result,wrong_anchor_controls=wrong,whole_root_bytes_and_full_modes_unchanged=True,mathematical_gates_assigned=False)
(D/'verification.json').write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n');print(json.dumps({k:v[k] for k in ['status','payload_files','payload_bytes','whole_root_files','directories_including_root','canonical_blobs','completed_originals_and_copies','whole_root_bytes_and_full_modes_unchanged']}))
