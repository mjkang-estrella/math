#!/usr/bin/env python3
"""Read-only Structural198 intake replay; mutations confined to tiny copies."""
from pathlib import Path
import datetime, hashlib, json, shutil, stat, subprocess, sys, tempfile
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]; R=C/'fresh-structural-discovery-r198'; K=R/'packet'
sha=lambda b:hashlib.sha256(b).hexdigest(); read=lambda p:json.loads(p.read_text())
anchors={'FINAL':'ac6274879d13d8ea654a939e5e4ccd71ec5725650d699314ee728faaed62e187','MANIFEST':'1495899e156902d42021ba7dc505b79bb143eb523d2c77a9ab334f3b525cacda','REPORT':'017d15d695a1b03f61c1e130c0c97a6f8065618ce5b2fe89ddea8532e23114ac'}
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
def verify(packet,report,a):
 return subprocess.run([sys.executable,'-I','-B',str(K/'authored/verify_packet.py'),'--packet',str(packet),'--report',str(report),'--final-sha256',a['FINAL'],'--manifest-sha256',a['MANIFEST'],'--report-sha256',a['REPORT']],capture_output=True,text=True,timeout=20)
before=inventory(R); v=verify(K,R/'REPORT.md',anchors); assert v.returncode==0,(v.stdout,v.stderr); vr=json.loads(v.stdout); assert (vr['selected_files'],vr['directories'])==(45,3)
for key,h in anchors.items():assert read(R/'ANCHORS.json')[key+'_SHA256']==h
manifest=read(K/'MANIFEST.json'); freeze=read(K/'private/freeze-anchor.json')
assert sha((K/'authored/SCOPE.md').read_bytes())==freeze['scope_sha256']==manifest['frozen_scope_sha256']
assert (K/'authored/SCOPE.md').stat().st_size==freeze['scope_bytes']==2013
assert sha((K/'authored/DERIVATIONS.md').read_bytes())==freeze['prefreeze_derivations_sha256']
assert freeze['frozen_utc']<manifest['sealed_utc']
for p in (K/'authored').iterdir():assert p.read_bytes()==(R/p.name).read_bytes()
assert (K/'FINAL.md').read_bytes()==(R/'FINAL.md').read_bytes()
tb=(PROJECT/'sources/preprints-tree.json').read_bytes(); assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb); assert not tree['truncated'] and len(tree['tree'])==13223
prefix='preprints/A-positive-solution-to-Tingleys-problem-September-23-2026/'
selection=[e for e in tree['tree'] if e['path'].startswith(prefix)]; assert sorted(selection,key=lambda e:e['path'])==sorted(read(K/'private/canonical-selected-tree.json'),key=lambda e:e['path'])
lookup={e['path']:e for e in selection if e['type']=='blob'}; auth=read(K/'private/authentication.json'); assert set(lookup)=={e['path'] for e in auth if e['path'].startswith(prefix)}
for e in auth:
 b=(K/e['local']).read_bytes(); assert len(b)==e['bytes'] and sha(b)==e['sha256']; assert b==(R/e['local']).read_bytes()
 if 'git_blob' in e:assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==lookup[e['path']]['sha']
comp=read(K/'private/comparator-auth.json'); b=(K/'private/TingleySphereIsometry.lean').read_bytes()
assert len(b)==comp['bytes'] and sha(b)==comp['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==comp['git_blob']
extents=read(K/'private/read-extents.json')
for e in extents:
 p=K/e['path']; assert len(p.read_bytes())==e['bytes'] and sha(p.read_bytes())==e['sha256']
 for a,b in e['ranges']:bounded(p,a,b)
 if e['complete']:
  assert e['ranges'][0][0]==0 and e['ranges'][-1][1]==e['bytes']
  assert all(x[1]==y[0] for x,y in zip(e['ranges'],e['ranges'][1:]))
for e in read(K/'private/primary-access.json'):
 if 'local' in e:
  p=K/e['local']; assert p.stat().st_size==e['bytes'] and sha(p.read_bytes())==e['sha256']
history=[('frontier/iterations/i13-fresh-discovery.md',1311,4107,'private/original-1.txt'),('frontier/iterations/i88-nonlinear-banach-discovery.md',1160,6224,'private/original-i88-scope.txt')]
for path,a,b,local in history:assert bounded(PROJECT/path,a,b)==(K/local).read_bytes()
for name in ['original-2.txt','original-3.txt']:assert not (K/'private'/name).exists()
assert bounded(PROJECT/'frontier/NEW-TEN-2026-10-14.md',4801,6347)==(K/'private/acceptance.bin').read_bytes()
assert bounded(PROJECT/'sources/CONTENTS.md',547380,548447)==(K/'private/source322-catalogue.bin').read_bytes()
control=read(K/'private/integrity-controls.json'); assert sha((K/'authored/verify_packet.py').read_bytes())==control['verifier_sha256']
ca={k.upper():v for k,v in control['anchors'].items()}; base=R/'private/integrity-controls'; controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as td:
 w=Path(td)/'root'; report=Path(td)/'REPORT.txt'; shutil.copy2(base/'REPORT.txt',report)
 def check(name,mut=None,wrong=None,expected=1):
  if w.exists():shutil.rmtree(w)
  shutil.copytree(base/'original',w)
  if mut:mut(w)
  snap=inventory(w); x=verify(w,report,wrong or ca); assert x.returncode==expected,(name,x.stdout,x.stderr); assert inventory(w)==snap
  controls.append({'case':name,'expected':expected,'actual':x.returncode})
 check('positive',expected=0)
 def change(w):
  p=w/'private/b.txt'; b=p.read_bytes();p.write_bytes(b'X'+b[1:])
 check('bytes',change);check('mode',lambda w:(w/'private/b.txt').chmod(0o644));check('extra',lambda w:(w/'extra.txt').write_text('extra'));check('missing',lambda w:(w/'private/b.txt').unlink())
 for key in ['MANIFEST','FINAL','REPORT']:check('wrong_'+key.lower()+'_anchor',wrong={**ca,key:'0'*64})
assert all(e['actual']==control['results'][e['case']]['exit'] for e in controls)
assert inventory(R)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':vr,'selected_files':45,'selected_directories':3,'selected_bytes':sum(e['bytes'] for e in manifest['files']),'root_files':sum(e['kind']=='file' for e in before.values()),'canonical_blobs':4,'read_extent_records':len(extents),'primary_pdf_bindings':4,'original_history_spans':2,'freeze':freeze,'author_proof_sha256':sha((K/'authored/AUTHOR-PROOF.md').read_bytes()),'author_proof_bytes':(K/'authored/AUTHOR-PROOF.md').stat().st_size,'controls':controls,'root_bytes_modes_unchanged':True,'verifier_scope':'Exact45-file packet plus separate MANIFEST inside packet and outside REPORT anchors;3 directories. Other root working copies/controls not included. Parent separately inventories entire root. Artifact checks do not certify semantic reading or mathematics.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n'); (P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n'); print(json.dumps(out,indent=2))
