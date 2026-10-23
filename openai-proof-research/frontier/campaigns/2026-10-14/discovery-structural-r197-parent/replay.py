#!/usr/bin/env python3
"""Read-only Structural197 intake replay; mutations confined to copied fixtures."""
from pathlib import Path
import datetime,hashlib,json,os,shutil,stat,subprocess,sys,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];R=C/'fresh-structural-discovery-r197';K=R/'packet'
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_text())
anchors={'FINAL':'3bd13bd00c9235659a14c08afd55a0ebef89009fd340161e0602e3753a832c5f','MANIFEST':'44faf9194caea0efe3cfd13c0feea525ce3d9987f682548a0d885b1ddc20598e','REPORT':'5eb22a0bbfd3d9e75e5aa029258ffdcfc0efda23803fef6b98e6fe19ce58f6ec'}
def inventory(root):
 out={}
 for p in [root,*root.rglob('*')]:
  s=p.lstat();assert not p.is_symlink();e={'mode':stat.S_IMODE(s.st_mode),'kind':'dir' if p.is_dir() else 'file'}
  if p.is_file():e.update(bytes=s.st_size,sha256=sha(p.read_bytes()))
  out[p.relative_to(root).as_posix()]=e
 return out
before=inventory(R)
def verify(root,a):
 return subprocess.run([sys.executable,'-I','-B',str(K/'verify_packet.py'),'--root',str(root),'--final-sha256',a['FINAL'],'--manifest-sha256',a['MANIFEST'],'--report-sha256',a['REPORT']],capture_output=True,text=True,timeout=20)
v=verify(R,anchors);assert v.returncode==0,(v.stdout,v.stderr);vr=json.loads(v.stdout);assert vr['files']==76
for label,e in read(R/'DETACHED.json').items():
 assert sha((R/e['path']).read_bytes())==e['sha256']
 if label in anchors:assert e['sha256']==anchors[label]
manifest=read(R/'MANIFEST.json');freeze=read(K/'private/freeze-anchor.json');assert freeze['sha256']==sha((K/'STATEMENT.txt').read_bytes());assert freeze['utc']<manifest['sealed_once_utc']
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree=json.loads(tb);assert not tree['truncated'];lookup={x['path']:x for x in tree['tree']}
for e in read(K/'private/source-authentication.json'):
 b=(K/e['local_path']).read_bytes();assert sha(b)==e['sha256'] and len(b)==e['bytes'];assert lookup[e['canonical_path']]['sha']==e['git_blob']==hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
for e in read(K/'private/source-read-extents.json')['reads']:
 if 'bytes' in e:assert e['bytes']==[0,(K/e['path']).stat().st_size]
 else:assert e['semantic']=='authenticated only; TeX is operative reading representation'
history=read(K/'private/history-read-extents.json')
for e in history:
 b=(PROJECT/e['path']).read_bytes()[slice(*e['bytes'])];assert b==(K/e['retained_file']).read_bytes() and sha(b)==e['selected_sha256']
for e in read(K/'private/primary-read-extents.json'):
 if 'file' in e and 'bytes' in e:
  p=K/e['file'];assert p.is_file();a,b=e['bytes'];assert 0<=a<=b<=p.stat().st_size
source_prefix='preprints/A-Counterexample-to-Walls-D2-Problem-October-6-2026/';assert {e['canonical_path'] for e in read(K/'private/source-authentication.json')}=={e['path'] for e in tree['tree'] if e['path'].startswith(source_prefix) and e['type']=='blob'}
ctrl=[];base=R/'controls';ca={'FINAL':sha((base/'packet/FINAL.txt').read_bytes()),'MANIFEST':sha((base/'MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.txt').read_bytes())}
with tempfile.TemporaryDirectory(prefix='copied-control-',dir=P) as td:
 w=Path(td)/'root'
 def check(name,mut=None,wrong=None,expected=1):
  if w.exists():shutil.rmtree(w)
  shutil.copytree(base,w)
  if mut:mut(w)
  snap=inventory(w);v=verify(w,wrong or ca);assert v.returncode==expected,(name,v.stdout,v.stderr);assert snap==inventory(w);ctrl.append({'case':name,'expected':expected,'actual':v.returncode})
 check('unchanged_copy',expected=0)
 def mutate(w):
  p=w/'packet/sample.txt';b=p.read_bytes();p.chmod(0o600);p.write_bytes(b'X'+b[1:]);p.chmod(0o444)
 check('selected_byte',mutate);check('selected_mode',lambda w:(w/'packet/sample.txt').chmod(0o600));check('extra_membership',lambda w:(w/'packet/extra').write_text('extra'));check('wrong_report_anchor',wrong={**ca,'REPORT':'0'*64});check('restored_copy',expected=0)
diag=subprocess.run([sys.executable,'-I','-B',str(K/'private/matrix-diagnostic.py')],capture_output=True,text=True,timeout=20);assert diag.returncode==0,diag.stderr;assert json.loads(diag.stdout)==read(K/'private/matrix-diagnostic.json')
assert inventory(R)==before
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':vr,'selected_files':76,'selected_bytes':sum(e['bytes'] for e in manifest['files']),'root_files':sum(e['kind']=='file' for e in before.values()),'canonical_blobs':10,'canonical_selection_exhausts_folder':True,'history_spans':len(history),'source_semantic_record_extents_bind_whole_files':True,'freeze':freeze,'author_proof_sha256':sha((K/'AUTHOR-PROOF.txt').read_bytes()),'author_proof_bytes':(K/'AUTHOR-PROOF.txt').stat().st_size,'controls':ctrl,'author_matrix_diagnostic_cases':len(json.loads(diag.stdout)['cases']),'root_bytes_modes_unchanged':True,'verifier_scope':'Exact selected packet and explicit detached FINAL/MANIFEST/REPORT; controls and DETACHED outside packet. Parent separately inventories entire current root. No mathematical grade.'}
(P/'replay.json').write_text(json.dumps(out,indent=2)+'\n');(P/'observed-root.json').write_text(json.dumps(before,indent=2)+'\n');print(json.dumps(out,indent=2))
