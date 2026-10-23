#!/usr/bin/env python3
"""Read-only contribution-packet bindings; controls mutate temporary copies only."""
from pathlib import Path
import datetime, hashlib, json, shutil, stat, subprocess, sys, tempfile
P=Path(__file__).resolve().parent; C=P.parents[1]; PROJECT=C.parents[2]
R=C/'structural-r198-contribution-r1'; K=R/'packet'; A=C/'fresh-structural-discovery-r198'; AK=A/'packet'; Q=K/'private'
read=lambda p:json.loads(p.read_text()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'3f6e6bf253bcbaba387a65ebd2fc5148523f3409b11f8bf81e66ffe2fa565c20','MANIFEST':'efdc8f348ff0172e3fe5b0f98ee335cbc998ff97be3675619bdfe90e01f5df0c','REPORT':'09638744acb9f6372739d4c8609759db181942a6e5ff6e520f14923c426bf5fa'}
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
   assert 0<=a<=b<=p.stat().st_size; f.seek(a); z=f.read(b-a); assert len(z)==b-a; data.append(z)
 return b''.join(data)
def verify(root,a):
 return subprocess.run([sys.executable,'-I','-B',str(K/'authored/verify_packet.py'),'--packet',str(root/'packet'),'--report',str(root/'REPORT.md'),'--final-sha256',a['FINAL'],'--manifest-sha256',a['MANIFEST'],'--report-sha256',a['REPORT']],capture_output=True,text=True,timeout=20)
before=inventory(R); ab=inventory(A); assert ab==read(P.parent/'observed-root.json')
recorded=read(Q/'author-readonly-inventory.json'); lookup={}
for kind,entries in [('file',recorded['files']),('dir',recorded['directories'])]:
 for e in entries:lookup[e['path']]={**{k:v for k,v in e.items() if k!='path'},'kind':kind}
assert lookup==ab
v=verify(R,anchors); assert v.returncode==0,(v.stdout,v.stderr); vr=json.loads(v.stdout)
assert (vr['selected_files'],vr['selected_directories'],vr['selected_bytes'])==(64,3,5046703)
assert all(read(R/'ANCHORS.json')[k+'_SHA256']==h for k,h in anchors.items())
m=read(K/'MANIFEST.json')
for name,key in [('SCOPE.md','frozen_scope_sha256'),('AUTHOR-PROOF.md','frozen_author_proof_sha256')]:
 b=(AK/'authored'/name).read_bytes(); assert b==(Q/('author-'+name)).read_bytes() and sha(b)==m[key]
tb=(PROJECT/'sources/preprints-tree.json').read_bytes(); assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb); assert not tree['truncated'] and len(tree['tree'])==13223
prefix='preprints/A-positive-solution-to-Tingleys-problem-September-23-2026/'
sel=[e for e in tree['tree'] if e['path'].startswith(prefix)]; cauth=read(Q/'canonical-authentication.json')
assert sorted(sel,key=lambda e:e['path'])==sorted(cauth['selected'],key=lambda e:e['path'])
blobs={e['path']:e for e in sel if e['type']=='blob'}
assert set(blobs)=={e['canonical'] for e in cauth['verified_blobs']}
for e in cauth['verified_blobs']:
 b=(Q/e['local']).read_bytes(); assert len(b)==e['bytes'] and sha(b)==e['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==blobs[e['canonical']]['sha']
comp=read(Q/'admitted-04-comparator-auth.json'); b=(Q/'TingleySphereIsometry.lean').read_bytes()
assert len(b)==comp['bytes'] and sha(b)==comp['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==comp['git_blob']
primary=0
for e in read(Q/'admitted-05-primary-access.json'):
 if 'local' in e:
  b=(K/e['local']).read_bytes(); assert b==(AK/e['local']).read_bytes() and sha(b)==e['sha256'] and len(b)==e['bytes']; primary+=1
for e in read(Q/'additional-primary-access.json'):
 for ext,key in [('pdf','pdf'),('txt','text')]:
  b=(Q/(e['name']+'.'+ext)).read_bytes(); assert len(b)==e[key+'_bytes'] and sha(b)==e[key+'_sha256']
 primary+=1
records=read(Q/'review-read-extents.json')
for e in records:
 b=(Q/e['retained']).read_bytes(); assert len(b)==e['retained_bytes'] and sha(b)==e['sha256']
 o=e['original']; ranges=e['semantic_extents_in_original']
 if o.startswith(('frontier/','AGENTS','sources/')): assert selected(PROJECT/o,ranges)==b
 elif o.startswith('author-packet '):assert selected(AK/o.removeprefix('author-packet '),ranges)==b
 elif ranges:assert all(0<=a<=z<=len(b) for a,z in ranges)
for e in read(Q/'author-read-extents.json'):
 b=selected(PROJECT/e['path'],[e['span']]); assert sha(b)==e['sha256']
brief=C/'expanded-target-2026-10-17/structural-r198-contribution-r1-brief.txt'; assert sha(brief.read_bytes())=='42cd9c761c583a89018934b49ed425b7df332425df5a13739f1c8cc7c3f9e184'
base=R/'controls/seed'; ca={'FINAL':sha((base/'packet/FINAL.md').read_bytes()),'MANIFEST':sha((base/'packet/MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())}; controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as td:
 w=Path(td)/'root'
 def check(name,mut=None,wrong=None,expected=1):
  if w.exists():shutil.rmtree(w)
  shutil.copytree(base,w)
  if mut:mut(w)
  snap=inventory(w); z=verify(w,wrong or ca); assert z.returncode==expected,(name,z.stdout,z.stderr); assert inventory(w)==snap
  controls.append({'case':name,'accepted':z.returncode==0,'expected':expected==0})
 check('unchanged',expected=0)
 def change(w):
  p=w/'packet/private/tiny-source.json'; b=p.read_bytes(); p.write_bytes(b'X'+b[1:])
 check('protected-byte',change); check('protected-mode',lambda w:(w/'packet/private/tiny-source.json').chmod(0o644)); check('extra-member',lambda w:(w/'packet/extra.txt').write_text('extra')); check('missing-member',lambda w:(w/'packet/private/tiny-source.json').unlink())
 for key in ['MANIFEST','FINAL','REPORT']:check('wrong-'+key.lower()+'-anchor',wrong={**ca,key:'0'*64})
assert [(e['case'],e['accepted']) for e in controls]==[(e['case'],e['expected_accept']) for e in read(Q/'integrity-controls.json')['copied_controls']]
assert inventory(R)==before and inventory(A)==ab
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':vr,'selected_files':64,'selected_directories':3,'selected_bytes':vr['selected_bytes'],'review_sha256':sha((K/'authored/REVIEW.md').read_bytes()),'review_bytes':(K/'authored/REVIEW.md').stat().st_size,'root_files':sum(e['kind']=='file' for e in before.values()),'author_root_files':117,'canonical_blobs':4,'primary_pdf_bindings':primary,'reading_record_bindings':len(records),'author_reading_record_bindings':len(read(Q/'author-read-extents.json')),'original_history_spans':2,'controls':controls,'author_and_reviewer_bytes_modes_unchanged':True,'scope':'Exact 64-file packet plus separate manifest and outside REPORT; full root inventories separate. Receipt binding is not semantic-reading certification or a mathematical grade.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n'); (P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n'); print(json.dumps(out,indent=2))
