#!/usr/bin/env python3
"""Read-only independent packet authentication; preserve the defective bundled verifier."""
from pathlib import Path, PurePosixPath
import hashlib,json,stat,subprocess,sys
P=Path(__file__).resolve().parents[4]; B=P/'frontier/campaigns/2026-10-14'; D=Path(__file__).resolve().parent; R=B/'fresh-arithmetic-discovery-r162au'
H={'final':'87ed5fc12864a5e711cf9751fece3b0922eb90a16a68bccb9a6373cf2b1c4e1c','manifest':'9debf0b0f5ab544dfc68392cbcab1e6fa392079e16b9c6dcf0e37fa932e907b2','report':'db541f7772dfaf87600d8b5dc1bd010de018fb4ff473f0a28cd234cf38319e1a'}
def sha(a): return hashlib.sha256(a).hexdigest()
def snap():
 out={}
 for f in R.rglob('*'):
  assert not f.is_symlink()
  assert f.is_file() or f.is_dir()
  if f.is_file():
   assert stat.S_ISREG(f.stat().st_mode)
   a=f.read_bytes();out[f.relative_to(R).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=f.stat().st_mode)
 return out
def member(n):
 q=PurePosixPath(n); assert n and not q.is_absolute() and '..' not in q.parts and q.as_posix()==n
 f=R/n
 for a in [f,*f.parents]:
  if a==R: break
  assert not a.is_symlink()
 assert stat.S_ISREG(f.lstat().st_mode)
 return f
vpath=R/'private/verify_packet.py'; code=vpath.read_text()
old="require(names==sorted(set(names)), 'unordered/duplicate member')"
new="require(len(names)==len(set(names)), 'duplicate member')"
assert code.count(old)==1
def run(h,corrected=False):
 args=[f'--{k}-sha256' for k in h]
 argv=[y for k in h for y in (f'--{k}-sha256',h[k])]
 if corrected:
  wrapper="from pathlib import Path\np=Path("+repr(str(vpath))+ ")\ns=p.read_text()\nassert s.count("+repr(old)+")==1\ns=s.replace("+repr(old)+","+repr(new)+",1)\nexec(compile(s,str(p),'exec'),{'__name__':'__main__','__file__':str(p)})"
  cmd=[sys.executable,'-I','-B','-c',wrapper,*argv]
 else: cmd=[sys.executable,'-I','-B',str(vpath),*argv]
 z=subprocess.run(cmd,cwd=P,capture_output=True,text=True)
 return dict(exit=z.returncode,stdout=z.stdout,stderr=z.stderr)
before=json.loads((D/'private/intake/root-before.json').read_text());assert snap()==before
original=run(H);assert original['exit']==1 and original['stderr'].strip()=='FAIL: unordered/duplicate member',original
corrected=run(H,True);assert corrected['exit']==0,corrected
for k,n in {'final':'private/FINAL.md','manifest':'private/MANIFEST.json','report':'REPORT.md'}.items():assert sha(member(n).read_bytes())==H[k]
m=json.loads(member('private/MANIFEST.json').read_text());assert m['schema']=='r162au-exact-packet-v1'
rows=m['files'];names=[r['path'] for r in rows];assert len(names)==len(set(names))==49 and names!=sorted(names)
assert set(before)==set(names)|{'private/MANIFEST.json','REPORT.md'}
for r in rows:
 f=member(r['path']);a=f.read_bytes()
 assert len(a)==r['bytes'] and sha(a)==r['sha256'] and stat.S_IMODE(f.stat().st_mode)==r['mode']
raw=(P/'sources/preprints-tree.json').read_bytes();assert sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
o=json.loads(raw);assert not o['truncated'];tree={x['path']:x for x in o['tree']}
local=json.loads(member('private/selected-tree.json').read_text());assert len(local)==20
prefix='preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/'
assert {x['path'] for x in local}=={x for x in tree if x==prefix[:-1] or x.startswith(prefix)}
for x in local:assert x==tree[x['path']]
bindings=[]
for x in json.loads(member('private/authentication.json').read_text()):
 assert x['path'].startswith(prefix)
 a=member('private/canonical/'+x['path'][len(prefix):]).read_bytes();g=hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()
 assert tree[x['path']]['type']=='blob' and len(a)==x['bytes']==tree[x['path']]['size'] and sha(a)==x['sha256'] and g==x['git_blob']==tree[x['path']]['sha']
 assert x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
 bindings.append(dict(path=x['path'],bytes=len(a),git_blob=g))
assert len(bindings)==15 and sum(x['bytes'] for x in bindings)==153982
inputs=json.loads((D/'private/completed-direct-inputs.json').read_text());assert len(inputs)==5
for x in inputs:
 f=P/x['path'];a=f.read_bytes();assert len(a)==x['bytes'] and sha(a)==x['sha256'] and f.stat().st_mode==x['mode']
for x in json.loads(member('private/completed-context/bindings.json').read_text()):
 a=member(x['copy']).read_bytes();assert a==(P/x['original']).read_bytes() and len(a)==x['bytes'] and sha(a)==x['sha256']
c=json.loads(member('private/integrity-controls/bindings.json').read_text());a=member(c['original']).read_bytes()
assert sha(a)==c['sha256'] and member(c['positive']).read_bytes()==a and sha(member(c['negative']).read_bytes())!=c['sha256']
controls=[]
for k in H:
 z=run({**H,k:'0'*64},True);assert z['exit']!=0 and 'detached anchor mismatch' in z['stderr'];controls.append(dict(name='wrong-'+k+'-anchor',**z))
assert snap()==before
out=dict(status='MATCH_WITH_BUNDLED_VERIFIER_DEFECT',anchors=H,payload=dict(files=len(rows),bytes=sum(x['bytes'] for x in rows)),whole_root_files=len(before),whole_root_bytes_and_full_modes_unchanged=True,canonical_text_bindings=bindings,canonical_tree_entries=len(local),scoped_lean_pointer='URL/SHA identity only; no independent preprint Git binding',completed_direct_inputs_unchanged=len(inputs),original_bundled_verifier=original,corrected_in_memory_verifier=corrected,correction=dict(original_file_sha256=sha(code.encode()),old=old,new=new,duplicate_rejection_preserved=True,exact_membership_independently_verified=True,original_file_not_modified=True),controls=controls,existing_copied_controls='positive matched; negative distinguished',no_mutation_recreated=True,artifact_check_only=True,parent_source_and_primary_proofs_reread=False)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','payload','whole_root_files','canonical_tree_entries','completed_direct_inputs_unchanged','artifact_check_only']}))
