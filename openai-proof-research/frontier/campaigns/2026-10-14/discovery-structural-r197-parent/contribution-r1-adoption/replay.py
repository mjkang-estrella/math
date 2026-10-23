#!/usr/bin/env python3
"""Read-only contribution artifact replay; mutations only in copied fixtures."""
from pathlib import Path
import datetime, hashlib, json, shutil, stat, subprocess, sys, tempfile
P=Path(__file__).resolve().parent; C=P.parents[1]; PROJECT=C.parents[2]
R=C/'structural-r197-contribution-r1'; K=R/'packet'; A=C/'fresh-structural-discovery-r197'; AK=A/'packet'
read=lambda p:json.loads(p.read_text()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'33a85a8a11a53edeeb0138534c2333caea31f991f5d161666624ac3a912701e9','MANIFEST':'bc64f8119d2cfe3aa49b3e122bfd80bfa2a3eda187bb26296c9e6e56552757ca','REPORT':'ec3593434bd7f0cfa55e390abd7ac974747f70388da73f537e4c64019f19c9ca'}
def inventory(root):
 out={}
 for p in [root,*root.rglob('*')]:
  s=p.lstat(); assert not p.is_symlink(); assert stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode)
  e={'mode':stat.S_IMODE(s.st_mode),'kind':'dir' if p.is_dir() else 'file'}
  if p.is_file():e.update(bytes=s.st_size,sha256=sha(p.read_bytes()))
  out[p.relative_to(root).as_posix()]=e
 return out
def bounded(p,a,b):
 assert 0<=a<=b<=p.stat().st_size
 with p.open('rb') as f:f.seek(a); data=f.read(b-a)
 assert len(data)==b-a
 return data
def verify(root,a):
 return subprocess.run([sys.executable,'-I','-B',str(K/'verify_packet.py'),'--root',str(root),'--final-sha256',a['FINAL'],'--manifest-sha256',a['MANIFEST'],'--report-sha256',a['REPORT']],capture_output=True,text=True,timeout=20)
before=inventory(R); ab=inventory(A); assert ab==read(P.parent/'observed-root.json')
recorded=read(K/'private/author-before.json'); assert set(ab)-{'.'}=={e['path'] for e in recorded}
for e in recorded:
 expected={k:v for k,v in e.items() if k not in ['path','type']}; expected['kind']=e['type']; assert ab[e['path']]==expected
assert read(K/'private/author-unchanged.json')['unchanged']
v=verify(R,anchors); assert v.returncode==0,(v.stdout,v.stderr); vr=json.loads(v.stdout); assert (vr['files'],vr['directories'])==(88,9)
assert all(read(R/'DETACHED.json')[k]==h for k,h in anchors.items())
for name in ['STATEMENT.txt','AUTHOR-PROOF.txt']:assert (AK/name).read_bytes()==(K/'private'/('frozen-'+name)).read_bytes()
tb=(PROJECT/'sources/preprints-tree.json').read_bytes(); assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb); assert not tree['truncated'] and len(tree['tree'])==13223
prefix='preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/'
sel=[e for e in tree['tree'] if e['path'].startswith(prefix)]; assert sorted(sel,key=lambda e:e['path'])==sorted(read(K/'private/source-tree.json'),key=lambda e:e['path'])
lookup={e['path']:e for e in sel if e['type']=='blob'}; source=read(K/'private/source-authentication.json'); assert set(lookup)=={e['canonical_path'] for e in source}
for e in source:
 b=(K/e['path']).read_bytes(); assert b==(AK/e['path']).read_bytes()
 assert sha(b)==e['sha256'] and len(b)==e['bytes']==lookup[e['canonical_path']]['size']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==lookup[e['canonical_path']]['sha']
for e in read(K/'private/source-read-extents.json'):
 p=K/e['path']; assert e['bytes']==[0,p.stat().st_size] and sha(p.read_bytes())==e['sha256']
for e in read(K/'private/primary-access.json'):
 p=K/'private/primary'/(e['name']+'.pdf'); assert p.stat().st_size==e['bytes'] and sha(p.read_bytes())==e['sha256'] and e['extract_exit']==0
 assert p.read_bytes()==(AK/'private/primary'/p.name).read_bytes()
primary=read(K/'private/primary-read-extents.json'); texts=set(); images=[]
for e in primary:
 p=K/e['path']
 if 'bytes' in e:
  assert sha(bounded(p,*e['bytes']))==e['span_sha256'] and sha(p.read_bytes())==e['extraction_sha256']
  assert p.read_bytes()==(AK/e['path']).read_bytes(); texts.add(e['path'])
 else:
  assert sha(p.read_bytes())==e['sha256']; images.append(e['path'])
  if 'howie-pages' in e['path']:assert p.read_bytes()==(AK/e['path']).read_bytes()
history=read(K/'private/history-read-extents.json'); ah=read(AK/'private/history-read-extents.json'); assert len(history)==len(ah)==20
for i,e in enumerate(history):
 assert (e['path'],e['bytes'],e['sha256'])==(ah[i]['path'],ah[i]['bytes'],ah[i]['selected_sha256'])
 b=bounded(PROJECT/e['path'],*e['bytes']); assert sha(b)==e['sha256'] and b==(AK/ah[i]['retained_file']).read_bytes()
 assert b==(K/'private/history-selected'/f'{i:02d}.txt').read_bytes()
direct=read(K/'private/direct-inputs.json')+read(K/'private/author-parent-read.json')
for e in direct:
 if 'path' in e:assert sha(bounded(PROJECT/e['path'],e['start'],e['end']))==e['sha256']
brief=C/'expanded-target-2026-10-17/structural-r197-contribution-r1-brief.txt'; assert sha(brief.read_bytes())=='4b3751fdd6d795b829a6d385e7d186c12580b34c2d74134af54ca115472ab67a'
assert brief.read_bytes()==(K/'private/brief.txt').read_bytes()
base=R/'private-controls'; ca={'FINAL':sha((base/'packet/FINAL.txt').read_bytes()),'MANIFEST':sha((base/'MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.txt').read_bytes())}; controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as td:
 w=Path(td)/'root'
 def check(name,mut=None,wrong=None,expected=1):
  if w.exists():shutil.rmtree(w)
  shutil.copytree(base,w)
  if mut:mut(w)
  snap=inventory(w); x=verify(w,wrong or ca); assert x.returncode==expected,(name,x.stdout,x.stderr); assert inventory(w)==snap
  controls.append({'case':name,'expected_success':expected==0,'observed_success':x.returncode==0})
 def change(w):
  p=w/'packet/sample.txt'; b=p.read_bytes(); p.chmod(0o600); p.write_bytes(b'X'+b[1:]); p.chmod(0o444)
 check('unchanged copied fixture',expected=0); check('one byte changed',change); check('mode changed',lambda w:(w/'packet/sample.txt').chmod(0o600)); check('extra membership',lambda w:(w/'packet/extra.txt').write_text('extra')); check('wrong detached REPORT anchor',wrong={**ca,'REPORT':'0'*64}); check('restored copied fixture',expected=0)
reported=read(K/'ARTIFACT-CONTROLS.json')['cases']; assert [(e['case'],e['observed_success']) for e in controls]==[(e['case'],e['observed_success']) for e in reported]
assert inventory(R)==before and inventory(A)==ab
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':vr,'selected_files':88,'selected_directories':9,'selected_bytes':sum(e['bytes'] for e in read(R/'MANIFEST.json')['files']),'review_sha256':sha((K/'REVIEW.txt').read_bytes()),'review_bytes':(K/'REVIEW.txt').stat().st_size,'canonical_blobs':10,'source_texts':9,'primary_texts':len(texts),'primary_images':len(images),'history_spans':20,'direct_inputs':sum('path' in e for e in direct),'root_files':sum(e['kind']=='file' for e in before.values()),'author_root_files':83,'controls':controls,'author_and_reviewer_bytes_modes_unchanged':True,'scope':'Artifact bindings and extents only, not semantic-reading certification or mathematical/contribution grade. Fresh Mannan image checked against own recorded hash; it differs from author render.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n'); (P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n'); print(json.dumps(out,indent=2))
