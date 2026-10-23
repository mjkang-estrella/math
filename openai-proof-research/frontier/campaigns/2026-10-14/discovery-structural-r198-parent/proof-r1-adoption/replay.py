#!/usr/bin/env python3
"""Read-only correctness-packet binding checks; mutate only copied controls."""
from pathlib import Path
import datetime, hashlib, json, shutil, stat, subprocess, sys, tempfile
P=Path(__file__).resolve().parent; C=P.parents[1]; PROJECT=C.parents[2]
R=C/'structural-r198-proof-r1'; K=R/'packet'; A=C/'fresh-structural-discovery-r198'; AK=A/'packet'
read=lambda p:json.loads(p.read_text()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'fa59f0e0ee588fd2b6b91ff517d040fe77e70a1dd5662ec5cc063aa68752185d','MANIFEST':'21d2c4338efac309ba5329ca616ba66c9c12be38a86eb9befd9c3447b6269c26','REPORT':'43cf6f3e3f94946566f05f0791659df3c804a7dfec740c6156398bd487480708'}
def inventory(root):
 out={}
 for p in [root,*root.rglob('*')]:
  s=p.lstat(); assert not p.is_symlink(); assert stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode)
  e={'mode':stat.S_IMODE(s.st_mode),'kind':'dir' if p.is_dir() else 'file'}
  if p.is_file():e.update(bytes=s.st_size,sha256=sha(p.read_bytes()))
  out[p.relative_to(root).as_posix()]=e
 return out
def selected(p,ranges):
 data=[]
 with p.open('rb') as f:
  for a,b in ranges:
   assert 0<=a<=b<=p.stat().st_size; f.seek(a); z=f.read(b-a); assert len(z)==b-a;data.append(z)
 return b''.join(data)
def verify(root,a):
 return subprocess.run([sys.executable,'-I','-B',str(K/'authored/verify_packet.py'),'--packet',str(root/'packet'),'--report',str(root/'REPORT.md'),'--final-sha256',a['FINAL'],'--manifest-sha256',a['MANIFEST'],'--report-sha256',a['REPORT']],capture_output=True,text=True,timeout=20)
before=inventory(R); ab=inventory(A); assert ab==read(P.parent/'observed-root.json')
recorded=read(K/'private/author-before.json'); lookup={e['path']:{k:v for k,v in e.items() if k!='path'} for e in recorded}
for e in lookup.values():
 if e['kind']=='directory':e['kind']='dir'
assert set(lookup)==set(ab)-{'.'}
assert all(ab[k]==v for k,v in lookup.items())
pres=read(K/'private/original-preservation.json'); assert pres['author_root_unchanged_bytes_modes'] and pres['files']==117
v=verify(R,anchors); assert v.returncode==0,(v.stdout,v.stderr);vr=json.loads(v.stdout);assert (vr['files'],vr['directories'])==(51,3)
assert all(read(R/'ANCHORS.json')[k+'_SHA256']==h for k,h in anchors.items())
m=read(K/'MANIFEST.json')
for name,key in [('SCOPE.md','frozen_scope_sha256'),('AUTHOR-PROOF.md','frozen_proof_sha256')]:
 b=(AK/'authored'/name).read_bytes(); assert b==(K/'private'/('author-'+name)).read_bytes() and sha(b)==m[key]
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb);assert not tree['truncated'] and len(tree['tree'])==13223
prefix='preprints/A-positive-solution-to-Tingleys-problem-September-23-2026/'
sel=[e for e in tree['tree'] if e['path'].startswith(prefix)];assert sorted(sel,key=lambda e:e['path'])==sorted(read(K/'private/canonical-selected-tree.json'),key=lambda e:e['path'])
blobs={e['path']:e for e in sel if e['type']=='blob'};auth=read(K/'private/authentication.json');assert set(blobs)=={e['path'] for e in auth if e['path'].startswith(prefix)}
for e in auth:
 b=(K/e['local']).read_bytes();assert b==(AK/e['local']).read_bytes() and len(b)==e['bytes'] and sha(b)==e['sha256']
 if 'git_blob' in e:assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==blobs[e['path']]['sha']
comp=read(K/'private/comparator-auth.json');b=(K/'private/TingleySphereIsometry.lean').read_bytes();assert len(b)==comp['bytes'] and sha(b)==comp['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==comp['git_blob']
for e in read(K/'private/primary-access.json'):
 if 'local' in e:
  b=(K/e['local']).read_bytes(); assert b==(AK/e['local']).read_bytes() and sha(b)==e['sha256'] and len(b)==e['bytes']
geher=read(K/'private/geher-access.json')
for ext in ['pdf','txt']:
 b=(K/'private'/('geher-1606.03584v1.'+ext)).read_bytes(); key='pdf' if ext=='pdf' else 'text';assert len(b)==geher[key+'_bytes'] and sha(b)==geher[key+'_sha256']
records=read(K/'private/reading-extents.json')['read_extents']
for e in records:
 b=selected(PROJECT/e['path'],e['ranges']);assert len(b)==e['selected_bytes'] and sha(b)==e['selected_sha256']
 local=K/e['local'];lb=local.read_bytes()
 if len(lb)!=e['selected_bytes']:
  assert e['local']=='private/geher-1606.03584v1.txt';lb=selected(local,e['ranges'])
 assert lb==b
assert read(K/'private/geher-selected-extents.json')['semantic_read']==records[-1]['ranges']
brief=C/'expanded-target-2026-10-17/structural-r198-proof-r1-brief.txt';assert sha(brief.read_bytes())=='5c5977817932d03bbe353b7112401b680206deb001d9ed05711e38320c17777e'
base=R/'controls/base';ca={'FINAL':sha((base/'packet/FINAL.md').read_bytes()),'MANIFEST':sha((base/'packet/MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())}; controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as td:
 w=Path(td)/'root'
 def check(name,mut=None,wrong=None,expected=1):
  if w.exists():shutil.rmtree(w)
  shutil.copytree(base,w)
  if mut:mut(w)
  snap=inventory(w);z=verify(w,wrong or ca);assert z.returncode==expected,(name,z.stdout,z.stderr);assert inventory(w)==snap
  controls.append({'case':name,'accepted':z.returncode==0,'expected':expected==0})
 check('unchanged',expected=0)
 def change(w):
  p=w/'packet/private/body.txt';b=p.read_bytes();p.write_bytes(b'X'+b[1:])
 check('private-byte',change);check('private-mode',lambda w:(w/'packet/private/body.txt').chmod(0o644));check('extra-file',lambda w:(w/'packet/extra.txt').write_text('extra'));check('missing-file',lambda w:(w/'packet/private/body.txt').unlink())
 for key in ['MANIFEST','FINAL','REPORT']:check('wrong-'+key.lower(),wrong={**ca,key:'0'*64})
assert [(e['case'],e['accepted']) for e in controls]==[(e['case'],e['accepted']) for e in read(K/'private/copied-controls.json')['controls']]
assert inventory(R)==before and inventory(A)==ab
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':vr,'selected_files':51,'selected_directories':3,'selected_bytes':sum(e['bytes'] for e in m['files']),'review_sha256':sha((K/'authored/REVIEW.md').read_bytes()),'review_bytes':(K/'authored/REVIEW.md').stat().st_size,'root_files':sum(e['kind']=='file' for e in before.values()),'author_root_files':117,'canonical_blobs':4,'primary_pdf_bindings':5,'reading_record_bindings':len(records),'original_history_spans':2,'controls':controls,'author_and_reviewer_bytes_modes_unchanged':True,'scope':'Exact51-file packet plus separate manifest and outside REPORT anchors; full root inventories separate. Source/primary/reading extent bindings are artifact evidence, not semantic-reading certification or a mathematical verdict.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n');print(json.dumps(out,indent=2))
