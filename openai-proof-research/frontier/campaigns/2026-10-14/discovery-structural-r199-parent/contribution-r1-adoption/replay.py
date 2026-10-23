#!/usr/bin/env python3
"""Read-only contribution review bindings; mutate only temporary copied controls."""
from pathlib import Path
import datetime, hashlib, json, shutil, stat, subprocess, sys, tempfile
P=Path(__file__).resolve().parent; C=P.parents[1]; PROJECT=C.parents[2]
R=C/'structural-r199-contribution-r1'; A=C/'fresh-structural-discovery-r199'; Q=R/'private'
read=lambda p:json.loads(p.read_text()); sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'022c237935d76ba8b86474f9cbab6a82283d781307def0749c85ddc3cd3ff5e4','MANIFEST':'d6c539287561a90887ae08790ee9aabd516b2896d0a516c695fabcc61a9f38d0','REPORT':'22d025347ec8e4db35452b9f3ab97305204a5964991742cc209d40986fd716e6'}
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
v=verify(R,anchors); assert v.returncode==0,(v.stdout,v.stderr); vr=json.loads(v.stdout)
assert (vr['selected_files'],vr['selected_directories'],vr['selected_bytes'])==(73,10,4729158)
assert all(read(R/'ANCHORS.json')[k+('.json' if k=='MANIFEST' else '.md')]==h for k,h in anchors.items())
intake=read(P.parent/'intake.json')
for name,key in [('frozen-statement.md','frozen_statement_sha256'),('author-proof.md','author_proof_sha256')]:
 b=(A/name).read_bytes(); assert b==(Q/'submitted'/name).read_bytes() and sha(b)==intake[key]
assert (Q/'receipts/author-MANIFEST.json').read_bytes()==(A/'MANIFEST.json').read_bytes()
assert (Q/'receipts/author-ANCHORS.json').read_bytes()==(A/'ANCHORS.json').read_bytes()
tb=(PROJECT/'sources/preprints-tree.json').read_bytes(); assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(tb); assert not tree['truncated'] and len(tree['tree'])==13223
prefix='preprints/Relative-independence-of-the-separable-quotient-problem-September-23-2026/'
blobs={e['path']:e for e in tree['tree'] if e['path'].startswith(prefix) and e['type']=='blob'}
auth=read(Q/'authentication.json'); assert auth['tree_sha256']==sha(tb) and auth['tree_bytes']==len(tb) and auth['tree_entries']==13223
receipts=auth['all_canonical_blobs']; assert set(blobs)=={e['canonical'] for e in receipts}
for e in receipts:
 p=PROJECT/e['admitted_local']; assert p.is_relative_to(A); b=p.read_bytes(); assert len(b)==e['bytes'] and sha(b)==e['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']==blobs[e['canonical']]['sha']
 own=Q/'source323'/e['canonical'].removeprefix(prefix)
 if own.exists():assert own.read_bytes()==b
for n,fn in [('lean-323-authentication.json','lean-323.md'),('comparator-authentication.json','SeparableQuotientNegative.lean')]:
 e=read(Q/'receipts'/n); b=(Q/'source323'/fn).read_bytes(); assert sha(b)==e['sha256'] and b==(A/'private'/fn).read_bytes()
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']
pc=0
for e in read(Q/'primary-authentication.json'):
 if 'prior_access_error' in e:continue
 b=(PROJECT/e['file']).read_bytes(); assert len(b)==e['bytes'] and sha(b)==e['sha256']; pc+=1
records=read(Q/'reading.json')['own_review_reads']; images=0
for e in records:
 p=PROJECT/e['source']
 if 'read_extent' in e:b=selected(p,*e['read_extent'])
 else:assert 'visual_read' in e; b=p.read_bytes();images+=1
 if 'sha256' in e:assert sha(b)==e['sha256']
 if 'copy' in e:own=R/e['copy']
 elif 'visual_read' in e:own=Q/'primary-images'/p.name
 else:assert e['read_extent']==[0,650];own=Q/'primary-selections'/f'{p.name}-0-650.txt'
 assert own.read_bytes()==b
 if e.get('LF_lines_one_based_half_open') is not None:
  lines=p.read_bytes().split(b'\n');a,z=e['LF_lines_one_based_half_open'];assert b==b'\n'.join(lines[a-1:z-1])+b'\n'
hr=read(Q/'original-reading.json')
for e in hr:
 b=selected(PROJECT/e['original'],*e['bytes_half_open']);assert b==(R/e['copy']).read_bytes() and sha(b)==e['sha256']
direct=read(Q/'initial-read.json')['acceptance'];assert sha(selected(PROJECT/direct['path'],*direct['span']))==direct['sha256']
brief=C/'expanded-target-2026-10-17/structural-r199-contribution-r1-brief.txt';assert sha(brief.read_bytes())=='e8a796f6520d60e9219e36bf86d04efd9cb1ee5b2c39b669c20f01c0c757dc27'
base=Q/'copied-controls/clean';ca={'FINAL':sha((base/'FINAL.md').read_bytes()),'MANIFEST':sha((base/'MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())};controls=[]
with tempfile.TemporaryDirectory(prefix='copied-controls-',dir=P) as td:
 w=Path(td)/'root'
 def check(name,mut=None,wrong=None,expected=1):
  if w.exists():shutil.rmtree(w)
  shutil.copytree(base,w)
  if mut:mut(w)
  snap=inventory(w);z=verify(w,wrong or ca);assert z.returncode==expected,(name,z.stdout,z.stderr);assert inventory(w)==snap
  controls.append({'case':name,'accepted':z.returncode==0,'expected':expected==0})
 check('clean',expected=0)
 def change(w):
  p=w/'payload.txt';b=p.read_bytes();om=stat.S_IMODE(p.stat().st_mode);p.chmod(0o600);p.write_bytes(b'X'+b[1:]);p.chmod(om)
 check('content-change',change);check('mode-change',lambda w:(w/'payload.txt').chmod(0o600));check('unexpected-member',lambda w:(w/'unexpected.txt').write_text('extra'));check('wrong-detached-anchor',wrong={**ca,'MANIFEST':'0'*64})
assert [(e['case'],e['accepted']) for e in controls]==[(e['case'],e['expected_returncode']==0) for e in read(Q/'copied-control-results.json')['controls']]
assert inventory(R)==before and inventory(A)==ab
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':vr,'selected_files':73,'selected_directories':10,'selected_bytes':vr['selected_bytes'],'review_sha256':sha((R/'REVIEW.md').read_bytes()),'review_bytes':(R/'REVIEW.md').stat().st_size,'root_files':sum(e['kind']=='file' for e in before.values()),'author_root_files':90,'canonical_blobs':14,'primary_pdf_bindings_to_author':pc,'reading_record_bindings':len(records),'primary_images':images,'history_spans':len(hr),'copied_controls':controls,'author_and_reviewer_bytes_modes_unchanged':True,'limits':'Exact selected packet plus detached anchors. Parent full-root baselines also checked. Receipt binding is not semantic reading or a mathematical verdict.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n');print(json.dumps(out,indent=2))
