#!/usr/bin/env python3
"""Read-only correctness-review bindings; mutate only temporary copied controls."""
from pathlib import Path
import datetime, hashlib, json, shutil, stat, subprocess, sys, tempfile
P=Path(__file__).resolve().parent; C=P.parents[1]; PROJECT=C.parents[2]
R=C/'structural-r199-proof-r1'; A=C/'fresh-structural-discovery-r199'; Q=R/'private'
read=lambda p:json.loads(p.read_text()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'51f66cc8834ab65f68b48f6764ddcf2990ad85e8d5c26b17d2c247dff8a05a5c','MANIFEST':'3f93a573ac038565f1ab69820524ee91a7c1e84ec75ea696c8b9d8f218dd783e','REPORT':'4c76a8ddb80cdce685a12eef53bde79cceb118ed6fd41513bf079c7fb22fd769'}
def inventory(root):
 out={}
 for p in [root,*root.rglob('*')]:
  s=p.lstat(); assert not p.is_symlink(); assert stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode)
  e={'mode':stat.S_IMODE(s.st_mode),'kind':'dir' if p.is_dir() else 'file'}
  if p.is_file():e.update(bytes=s.st_size,sha256=sha(p.read_bytes()))
  out[p.relative_to(root).as_posix()]=e
 return out
def selected(p,a,b):
 with p.open('rb') as f:f.seek(a); z=f.read(b-a)
 assert len(z)==b-a; return z
def verify(root,an):
 return subprocess.run([sys.executable,'-I','-B',str(R/'verify-packet.py'),'--root',str(root),'--final-sha256',an['FINAL'],'--manifest-sha256',an['MANIFEST'],'--report-sha256',an['REPORT']],capture_output=True,text=True,timeout=30)
before=inventory(R); ab=inventory(A); assert ab==read(P.parent/'observed-root.json')
rec=read(Q/'author-inventory-before.json'); lookup={}
for e in rec:
 lookup[e['path']]={k:v for k,v in e.items() if k!='path'}; lookup[e['path']]['mode']=int(e['mode'],8)
 if e['kind']=='directory':lookup[e['path']]['kind']='dir'
assert set(lookup)==set(ab)-{'.'} and all(ab[k]==v for k,v in lookup.items())
pres=read(Q/'author-unchanged.json'); assert pres['all_90_files_and_12_directory_inventory_unchanged'] and pres['before_inventory_sha256']==sha((Q/'author-inventory-before.json').read_bytes())
v=verify(R,anchors); assert v.returncode==0,(v.stdout,v.stderr); vr=json.loads(v.stdout)
assert (vr['selected_files'],vr['selected_directories'],vr['selected_bytes'])==(67,10,5274721)
assert all(read(R/'ANCHORS.json')[k+('.json' if k=='MANIFEST' else '.md')]==h for k,h in anchors.items())
m=read(R/'MANIFEST.json'); intake=read(P.parent/'intake.json')
for name,key in [('frozen-statement.md','frozen_statement_sha256'),('author-proof.md','author_proof_sha256')]:
 b=(A/name).read_bytes(); assert b==(Q/'author-inputs'/name).read_bytes() and sha(b)==intake[key]
tb=(PROJECT/'sources/preprints-tree.json').read_bytes(); assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb); assert not tree['truncated'] and len(tree['tree'])==13223
prefix='preprints/Relative-independence-of-the-separable-quotient-problem-September-23-2026/'
sel=[e for e in tree['tree'] if e['path'].startswith(prefix)]; assert sel==read(Q/'canonical-tree-selection.json')['entries']
blobs={e['path']:e for e in sel if e['type']=='blob'}; receipts=read(Q/'source-authentication.json'); assert set(blobs)=={e['canonical_path'] for e in receipts}
for e in receipts:
 p=PROJECT/e['own_path']; assert p.is_relative_to(R); b=p.read_bytes(); assert b==(PROJECT/e['author_path']).read_bytes() and len(b)==e['bytes'] and sha(b)==e['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==blobs[e['canonical_path']]['sha']
for e in read(Q/'comparator-authentication.json'):
 b=(R/e['path']).read_bytes(); assert b==(A/e['path']).read_bytes() and sha(b)==e['sha256']; assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']
pc=0
for e in read(Q/'primary-authentication.json')['items']:
 if 'error' in e:continue
 b=(A/'private/primary'/e['file']).read_bytes(); assert len(b)==e['bytes'] and sha(b)==e['sha256']; pc+=1
pr=[]
for n in ['primary-reading-1.json','primary-reading-2.json','primary-reading-3.json']:
 for e in read(Q/n):
  original=PROJECT/e['author_path']; b=selected(original,*e['bytes_half_open']); assert sha(original.read_bytes())==e['full_file_sha256'] and sha(b)==e['selected_sha256'] and b==(PROJECT/e['own']).read_bytes(); pr.append(e)
hr=read(Q/'history-reading.json')
for e in hr:
 b=selected(PROJECT/e['original'],*e['bytes_half_open']); assert b==(PROJECT/e['own']).read_bytes() and sha(b)==e['sha256']
imgs=read(Q/'jr-visual-reading.json')['images']
for e in imgs:
 b=(PROJECT/e['author_path']).read_bytes(); assert b==(PROJECT/e['own_path']).read_bytes() and len(b)==e['bytes'] and sha(b)==e['sha256']
subs=read(Q/'submission-reading.json')
for e in subs:
 p=PROJECT/e['path']; b=p.read_bytes(); assert len(b)==e['bytes'] and sha(b)==e['sha256']
 own=Q/('author-inputs' if p.parent==A else 'parent-inputs')/p.name; assert own.read_bytes()==b
sr=read(Q/'reading-and-access.json')['source']
for e in sr:
 p=PROJECT/e['own_path']; assert sha(p.read_bytes())==e['sha256']
 if e['semantic_extent_bytes'] is not None: assert selected(p,*e['semantic_extent_bytes'])==p.read_bytes()
assert selected(PROJECT/'frontier/NEW-TEN-2026-10-14.md',4801,6347)==(Q/'acceptance-slice.txt').read_bytes()
brief=C/'expanded-target-2026-10-17/structural-r199-proof-r1-brief.txt'; assert sha(brief.read_bytes())=='0ce379aee62c4e952fd02a6ed331a883d7c39d186a8286365d6d99e414826d0a'
base=Q/'copied-controls/unchanged'; ca={'FINAL':sha((base/'FINAL.md').read_bytes()),'MANIFEST':sha((base/'MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())}; controls=[]
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
  p=w/'payload.txt'; b=p.read_bytes(); om=stat.S_IMODE(p.stat().st_mode); p.chmod(0o600); p.write_bytes(b'X'+b[1:]); p.chmod(om)
 check('changed-content',change); check('changed-mode',lambda w:(w/'payload.txt').chmod(0o600)); check('unexpected-member',lambda w:(w/'unexpected.txt').write_text('extra')); check('wrong-anchor',wrong={**ca,'MANIFEST':'0'*64})
assert [(e['case'],e['accepted']) for e in controls]==[(e['case'],e['expected']=='OK') for e in read(Q/'copied-control-results.json')['controls']]
assert inventory(R)==before and inventory(A)==ab
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':vr,'selected_files':67,'selected_directories':10,'selected_bytes':vr['selected_bytes'],'review_sha256':sha((R/'REVIEW.md').read_bytes()),'review_bytes':(R/'REVIEW.md').stat().st_size,'root_files':sum(e['kind']=='file' for e in before.values()),'author_root_files':90,'canonical_blobs':14,'primary_pdf_bindings_to_author':pc,'primary_text_span_bindings':len(pr),'primary_images':len(imgs),'source_text_bindings':sum(e['semantic_extent_bytes'] is not None for e in sr),'submission_bindings':len(subs),'history_spans':len(hr),'copied_controls':controls,'author_and_reviewer_bytes_modes_unchanged':True,'limits':'Exact selected review packet plus explicit detached anchors; full root inventories separate. Binding primary/source/history receipts is not semantic-reading certification or a mathematical verdict.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n'); (P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n'); print(json.dumps(out,indent=2))
