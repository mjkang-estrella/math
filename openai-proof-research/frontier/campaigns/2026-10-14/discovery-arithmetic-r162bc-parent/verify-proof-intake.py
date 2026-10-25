#!/usr/bin/env python3
"""Authenticate completed correctness review and immutable author inputs read-only."""
from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent;R=B/'arithmetic-r162bc-proof-r1';A=B/'fresh-arithmetic-discovery-r162bc'
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
anchors={'final':'cf16edf73eab567495a0e35306586de8468b8b7cb2c4efe6fb259a250042c6ed','manifest':'6b1945ce10d6cca99c99b92a992d1947685a4d7c7c03c5499c9944d2f0ec1aa3','report':'d2739a1e56c7e3c106786f84871f320e1b785341939fb6fa6a319148e1e56c4a'}
paths={'final':'private/FINAL.md','manifest':'private/MANIFEST.json','report':'REPORT.md'}
before=read(D/'private/proof-intake/root-before.json');assert snap(R)==before
for k,n in paths.items():assert sha((R/n).read_bytes())==anchors[k]
cmd=['python','-I','-B',str(R/'private/verify.py'),'--root',str(R)]
for k,v in anchors.items():cmd+=['--'+k,v]
run=subprocess.run(cmd,cwd=P,capture_output=True,text=True);assert run.returncode==0,run.stderr
result=json.loads(run.stdout);assert result==dict(payload_files=79,whole_root_files=82,directories_including_root=16)
m=read(R/'private/MANIFEST.json');fp=[e['path'] for e in m['files']];dp=[e['path'] for e in m['directories']]
assert fp==sorted(fp) and len(fp)==len(set(fp)) and dp==sorted(dp) and len(dp)==len(set(dp))
assert len({n.casefold() for n in fp+list(paths.values())})==len(fp)+3
for n in fp+dp:
 if n=='.':assert n in dp;continue
 p=PurePosixPath(n);assert n and '\\' not in n and '\0' not in n and not p.is_absolute() and str(p)==n and all(x not in {'.','..',''} for x in n.split('/'))
assert set(before)==set(fp)|set(paths.values())
actual_dirs={'.':R.stat().st_mode,**{f.relative_to(R).as_posix():f.stat().st_mode for f in R.rglob('*') if f.is_dir()}}
assert m['directories']==[dict(path=n,mode=actual_dirs[n]) for n in sorted(actual_dirs)]
for e in m['files']:
 f=R/e['path'];a=f.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and f.stat().st_mode==e['mode']
for n,mode in m['anchor_modes'].items():assert (R/n).stat().st_mode==mode
author_before=read(D/'private/intake/root-before.json');assert len(author_before)==66 and snap(A)==author_before
admitted=read(R/'private/admitted-author-inputs.json');inputs=read(R/'private/author-inputs.json');copies=read(R/'private/copy-bindings.json')
assert len(inputs)==66 and len(admitted)==46 and len(copies)==46 and len({x['copy'] for x in copies})==46
expected_inputs=[dict(path=(A/n).relative_to(P).as_posix(),**e) for n,e in sorted(author_before.items())]
assert inputs==expected_inputs and {e['original'] for e in copies}=={e['path'] for e in admitted}
ib={e['path']:e for e in admitted}
for e in copies:
 z=ib[e['original']];f=P/e['original'];a=f.read_bytes();c=R/e['copy'];assert a==c.read_bytes()
 assert len(a)==e['bytes']==z['bytes'] and sha(a)==e['sha256']==z['sha256'] and f.stat().st_mode==c.stat().st_mode==e['mode']==z['mode']
tree_bytes=(R/'private/complete-tree.json').read_bytes();assert sha(tree_bytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tree_bytes);assert not tree['truncated'];tb={e['path']:e for e in tree['tree']};source=read(R/'private/source-auth.json')['entries'];assert len(source)==16
for e in source:
 z=tb[e['path']];assert all(e[k]==z[k] for k in ['path','mode','type','sha'])
 if e['type']=='blob':assert e['size']==z['size']
assert len([e for e in source if e['type']=='blob'])==12
assert sha((A/'private/STATEMENT.md').read_bytes())=='ffb70a869024e8ebf88964edb0a41575d2d3922976579e93dd593a2d4ed3f528'
assert sha((A/'private/PROOF.md').read_bytes())=='dc51e6cc034a28da0f229bae81f85a00eee98be03d3dc9afe26521165f055fca'
ns={'__name__':'parent_readonly_review_authentication'};exec(compile((R/'private/verify.py').read_text(),str(R/'private/verify.py'),'exec'),ns)
wrong=[]
for k in anchors:
 a=dict(anchors);a[k]='0'*64
 try:ns['verify'](R,a)
 except AssertionError as exc:assert 'anchor mismatch' in str(exc);wrong.append(dict(anchor=k,rejected=str(exc)))
 else:raise AssertionError('wrong anchor accepted')
fixture=R/'private/controls/fixture';fixture_result=ns['verify'](fixture,{k:sha((fixture/n).read_bytes()) for k,n in paths.items()})
controls=read(R/'private/artifact-controls.json');assert len(controls)==5 and sum('rejected' in e for e in controls)==3
assert snap(R)==before and snap(A)==author_before
v=dict(status='MATCH',artifact_only=True,bundled_verifier_passed=True,bundled_verifier=dict(returncode=run.returncode,stdout=run.stdout,stderr=run.stderr,sha256=sha((R/'private/verify.py').read_bytes())),independent_exact_membership_hash_length_full_mode_check=True,payload_files=79,payload_bytes=sum(e['bytes'] for e in m['files']),whole_root_files=82,directories_including_root=16,subdirectories=15,canonical_blobs=12,canonical_entries=16,admitted_author_copies=46,author_original_files=66,statement_sha256=sha((A/'private/STATEMENT.md').read_bytes()),proof_sha256=sha((A/'private/PROOF.md').read_bytes()),review_sha256=sha((R/'private/REVIEW.md').read_bytes()),anchors=anchors,author_copied_controls=controls,intact_fixture_readonly_recheck=fixture_result,wrong_anchor_controls=wrong,review_root_bytes_and_full_modes_unchanged=True,author_root_bytes_and_full_modes_unchanged=True,no_contribution_or_acceptance_grade_from_artifact_checks=True)
(D/'proof-verification.json').write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n');print(json.dumps({k:v[k] for k in ['status','payload_files','payload_bytes','whole_root_files','directories_including_root','admitted_author_copies','author_original_files','review_root_bytes_and_full_modes_unchanged','author_root_bytes_and_full_modes_unchanged']}))
