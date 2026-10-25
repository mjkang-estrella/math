#!/usr/bin/env python3
"""Read-only authentication of full-scope contribution review; no math gate from bytes."""
from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent;R=B/'arithmetic-r162bc-contribution-r1';A=B/'fresh-arithmetic-discovery-r162bc'
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
anchors={'private/FINAL.md':'80cea4bf5474f3def1026b606d6232f3108869509ed45e16f22e4e27fb7d090e','private/MANIFEST.json':'a5afcf85ef9aaed7da9344458cd05dc1d6115509cfaf8e4a1f216c94ba5900b9','REPORT.md':'e252a74e3f36a7eb72c2f6360f2e5fcd67458aa59f58f2fed270305ef21d408b'}
before=read(D/'private/contribution-intake/root-before.json');assert snap(R)==before
for n,h in anchors.items():assert sha((R/n).read_bytes())==h
cmd=['python','-I','-B',str(R/'private/verify.py'),'--root',str(R),'--final',anchors['private/FINAL.md'],'--manifest',anchors['private/MANIFEST.json'],'--report',anchors['REPORT.md']]
run=subprocess.run(cmd,cwd=P,capture_output=True,text=True);assert run.returncode==0,run.stderr;result=json.loads(run.stdout)
assert result['verified'] and result['files']==88
m=read(R/'private/MANIFEST.json');fp=[e['path'] for e in m['files']];dp=[e['path'] for e in m['directories']]
assert fp==sorted(fp) and len(fp)==len(set(fp)) and dp==sorted(dp) and len(dp)==len(set(dp))
assert set(before)==set(fp)|{'private/MANIFEST.json'} and len(fp)==87
assert len({n.casefold() for n in fp+['private/MANIFEST.json']})==88
for n in fp+dp:
 if n=='.':assert n in dp;continue
 p=PurePosixPath(n);assert n and '\\' not in n and '\0' not in n and not p.is_absolute() and str(p)==n and all(x not in {'.','..',''} for x in n.split('/'))
actual_dirs={'.':R.stat().st_mode,**{f.relative_to(R).as_posix():f.stat().st_mode for f in R.rglob('*') if f.is_dir()}}
assert m['directories']==[dict(path=n,mode=actual_dirs[n]) for n in sorted(actual_dirs)]
assert len((R/'private/MANIFEST.json').read_bytes())==m['self_bytes'] and (R/'private/MANIFEST.json').stat().st_mode==m['self_mode']
for e in m['files']:
 f=R/e['path'];a=f.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and f.stat().st_mode==e['mode']
author_before=read(D/'private/intake/root-before.json');assert len(author_before)==66 and snap(A)==author_before
inputs=read(R/'private/author-inputs.json');admitted=read(R/'private/admitted-author-inputs.json');assert len(inputs)==66 and len(admitted)==46
assert inputs==[dict(path=(A/n).relative_to(P).as_posix(),**e) for n,e in sorted(author_before.items())]
for e in admitted:
 f=P/e['path'];rel=f.relative_to(A);c=R/'private/admitted'/rel;a=f.read_bytes();assert a==c.read_bytes()
 assert len(a)==e['bytes'] and sha(a)==e['sha256'] and f.stat().st_mode==c.stat().st_mode==e['mode']
tree_bytes=(P/'sources/preprints-tree.json').read_bytes();assert sha(tree_bytes)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tree_bytes);assert not tree['truncated'];tb={e['path']:e for e in tree['tree']};source=read(R/'private/source-auth.json')['entries'];assert len(source)==16
for e in source:
 z=tb[e['path']];assert all(e[k]==z[k] for k in ['path','mode','type','sha'])
 if e['type']=='blob':assert e['size']==z['size']
assert len([e for e in source if e['type']=='blob'])==12
assert sha((A/'private/STATEMENT.md').read_bytes())=='ffb70a869024e8ebf88964edb0a41575d2d3922976579e93dd593a2d4ed3f528'
assert sha((A/'private/PROOF.md').read_bytes())=='dc51e6cc034a28da0f229bae81f85a00eee98be03d3dc9afe26521165f055fca'
ns={'__name__':'parent_readonly_contribution_authentication'};exec(compile((R/'private/verify.py').read_text(),str(R/'private/verify.py'),'exec'),ns)
wrong=[]
for n in anchors:
 a=dict(anchors);a[n]='0'*64
 try:ns['verify'](R,a)
 except ValueError as exc:assert 'anchor mismatch' in str(exc);wrong.append(dict(anchor=n,rejected=str(exc)))
 else:raise AssertionError('wrong anchor accepted')
fixture=R/'private/controls/positive';fixture_result=ns['verify'](fixture,{n:sha((fixture/n).read_bytes()) for n in anchors})
assert snap(R)==before and snap(A)==author_before
assert snap(B/'arithmetic-r162bc-proof-r1')==read(D/'private/proof-intake/root-before.json')
v=dict(status='MATCH',artifact_only=True,bundled_verifier_passed=True,bundled_verifier=dict(returncode=run.returncode,stdout=run.stdout,stderr=run.stderr,sha256=sha((R/'private/verify.py').read_bytes())),manifest_records=87,manifest_records_include_final_and_report=True,payload_files_excluding_three_envelopes=85,payload_bytes_excluding_three_envelopes=sum(e['bytes'] for e in m['files'] if e['path'] not in anchors),whole_root_files=88,directories_including_root=len(dp),canonical_blobs=12,canonical_entries=16,admitted_author_copies=46,author_original_files=66,statement_sha256=sha((A/'private/STATEMENT.md').read_bytes()),proof_sha256=sha((A/'private/PROOF.md').read_bytes()),integrated_comparison_sha256=sha((R/'private/INTEGRATED-COMPARISON.md').read_bytes()),primary_comparison_sha256=sha((R/'private/PRIMARY-COMPARISON.md').read_bytes()),anchors=anchors,intact_copied_fixture_readonly_recheck=fixture_result,wrong_anchor_controls=wrong,independent_exact_membership_hash_length_full_mode_check=True,review_root_bytes_and_full_modes_unchanged=True,author_root_bytes_and_full_modes_unchanged=True,correctness_review_seal_unchanged=True,no_mathematical_grade_from_artifact_checks=True)
(D/'contribution-verification.json').write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n');print(json.dumps({k:v[k] for k in ['status','manifest_records','whole_root_files','payload_files_excluding_three_envelopes','payload_bytes_excluding_three_envelopes','directories_including_root','admitted_author_copies','author_original_files','review_root_bytes_and_full_modes_unchanged']}))
