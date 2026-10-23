#!/usr/bin/env python3
"""Read-only sealed-author intake; only temporary copied controls are mutated."""
from pathlib import Path
import datetime, hashlib, json, shutil, stat, subprocess, sys, tempfile
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]; A=C/'fresh-structural-discovery-r199'
read=lambda p:json.loads(p.read_text()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'3cedebb66c92b6bc22e99c666dc9fb66535d448999e4f026b8da3a86bb74c357','MANIFEST':'e6672dce587e59b6950f96aa0456a967d00384fab9bf4284eefe0c14d19d125a','REPORT':'8841be879a402872d7f91e61e05d8f9bed9ddc2eb8dc990234e9efea54762aa0'}
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
 return subprocess.run([sys.executable,'-I','-B',str(A/'verify-packet.py'),'--root',str(root),'--final-sha256',an['FINAL'],'--manifest-sha256',an['MANIFEST'],'--report-sha256',an['REPORT']],capture_output=True,text=True,timeout=30)
before=inventory(A); v=verify(A,anchors); assert v.returncode==0,(v.stdout,v.stderr); vr=json.loads(v.stdout)
assert (vr['selected_files'],vr['selected_directories'])==(70,7)
assert all(read(A/'ANCHORS.json')[k+('.json' if k=='MANIFEST' else '.md')]==h for k,h in anchors.items())
m=read(A/'MANIFEST.json'); members={e['path']:e for e in m['files']}
fr=read(A/'private/freeze-anchor.json'); assert sha((A/fr['statement']).read_bytes())==fr['sha256'] and (A/fr['statement']).stat().st_size==fr['bytes']
tb=(PROJECT/'sources/preprints-tree.json').read_bytes(); assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb); assert not tree['truncated'] and len(tree['tree'])==13223
prefix='preprints/Relative-independence-of-the-separable-quotient-problem-September-23-2026/'
sel=[e for e in tree['tree'] if e['path'].startswith(prefix)]; assert sel==read(A/'private/canonical-tree-selection.json')['selected_entries']
blobs={e['path']:e for e in sel if e['type']=='blob'}; receipts=read(A/'private/source-authentication.json')['blobs']; assert set(blobs)=={e['path'] for e in receipts}
for e in receipts:
 p=PROJECT/e['local']; assert p.is_relative_to(A); b=p.read_bytes(); assert len(b)==e['bytes'] and sha(b)==e['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==blobs[e['path']]['sha']
for n,fn in [('lean-323-authentication.json','lean-323.md'),('comparator-authentication.json','SeparableQuotientNegative.lean')]:
 e=read(A/'private'/n); b=(A/'private'/fn).read_bytes(); assert sha(b)==e['sha256'] and len(b)==e['metadata']['size']; assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==e['metadata']['sha']
sr=read(A/'private/source-reading.json')
for e in sr['reads']:
 b=selected(A/e['file'],*e['semantic_extent_bytes']); assert sha(b)==e['sha256']; assert len(b)==members[e['file']]['bytes']
primary=read(A/'private/primary/access.json')['items']+read(A/'private/primary/access-second.json'); pc=0
for e in primary:
 if 'error' in e:continue
 b=(A/'private/primary'/e['file']).read_bytes(); assert len(b)==e['bytes'] and sha(b)==e['sha256']; pc+=1
pr=read(A/'private/primary-reading.json')
for e in pr:
 assert e['file'] in members
 if 'bytes_half_open' in e:
  b=selected(A/e['file'],*e['bytes_half_open']); assert b
  if 'LF_lines_half_open' in e:
   # The receipt's half-open LF line numbers are one-based; byte offsets are zero-based.
   lines=(A/e['file']).read_bytes().split(b'\n'); a,z=e['LF_lines_half_open']; assert b==b'\n'.join(lines[a-1:z-1])+b'\n'
hr=read(A/'private/history-read-extents.json')
for e in hr:
 b=selected(PROJECT/e['original'],*e['extent_bytes']); assert b==(PROJECT/e['copied_to']).read_bytes() and sha(b)==e['sha256']
assert selected(PROJECT/'frontier/NEW-TEN-2026-10-14.md',4801,6347)==(A/'private/acceptance-slice.txt').read_bytes()
assert selected(PROJECT/'sources/CONTENTS.md',548447,549528)==(A/'private/catalogue-source323.txt').read_bytes()
base=A/'private/copied-controls/baseline'; ca={'FINAL':sha((base/'FINAL.md').read_bytes()),'MANIFEST':sha((base/'MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())}; controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as td:
 w=Path(td)/'root'
 def check(name,mut=None,wrong=None,expected=1):
  if w.exists():shutil.rmtree(w)
  shutil.copytree(base,w)
  if mut:mut(w)
  snap=inventory(w); z=verify(w,wrong or ca); assert z.returncode==expected,(name,z.stdout,z.stderr); assert inventory(w)==snap
  controls.append({'case':name,'accepted':z.returncode==0,'expected':expected==0})
 check('untouched small copied control',expected=0)
 def change(w):
  p=w/'payload.txt'; b=p.read_bytes(); original_mode=stat.S_IMODE(p.stat().st_mode)
  p.chmod(0o600); p.write_bytes(b'X'+b[1:]); p.chmod(original_mode)
 check('changed-content',change); check('changed-mode',lambda w:(w/'payload.txt').chmod(0o600)); check('unexpected-member',lambda w:(w/'unexpected.txt').write_text('extra')); check('wrong explicit detached anchor',wrong={**ca,'MANIFEST':'0'*64})
assert [(e['case'],e['accepted']) for e in controls]==[(e['case'],e['expected_returncode']==0) for e in read(A/'private/copied-control-results.json')['results']]
assert inventory(A)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':vr,'selected_files':70,'selected_directories':7,'selected_bytes':sum(e['bytes'] for e in m['files']),'root_files':sum(e['kind']=='file' for e in before.values()),'root_directories':sum(e['kind']=='dir' for e in before.values()),'frozen_statement':fr,'author_proof_sha256':sha((A/'author-proof.md').read_bytes()),'canonical_blobs':14,'source_and_comparator_reading_bindings':len(sr['reads']),'primary_pdf_bindings':pc,'primary_reading_records':len(pr),'history_spans':len(hr),'copied_controls':controls,'author_root_bytes_modes_unchanged':True,'limitations':'Receipt/extent binding is not semantic reading or a mathematical verdict. Parent did not reread primary/source/history bodies in this intake.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n'); (P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n'); print(json.dumps(out,indent=2))
