#!/usr/bin/env python3
"""Read-only contribution artifact intake, preserving the correctness condition."""
from pathlib import Path
import datetime,hashlib,json,os,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];R=C/'structural-r220-contribution-r1';Q=R/'packet/private';A=C/'fresh-structural-discovery-r220'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'3620105539e3130cff4908e334bd31519123e5ca04d1e596fa535dd9b3620c49','MANIFEST':'cb6db7720ad166a5566eb48b5d3da58802b4659cf36be6d937ea3145205c13f0','REPORT':'144e00a7843de026b2343ffb853953f546798e5eb069aa93e2a80c35b3fa89a9'}
def observe(root):
 out={}
 for parent,dirs,files in os.walk(root,followlinks=False):
  for p in [Path(parent),*(Path(parent)/n for n in files)]:
   assert not p.is_symlink();e={'type':'directory' if p.is_dir() else 'file','mode':format(stat.S_IMODE(p.stat().st_mode),'04o')}
   if p.is_file():b=p.read_bytes();e.update(bytes=len(b),sha256=sha(b))
   out[p.relative_to(root).as_posix()]=e
  assert all(not (Path(parent)/n).is_symlink() for n in dirs)
 return out
def run(root,a):
 return subprocess.run(['python3','-I','-B',str(R/'packet/verify_selection.py'),'--root',str(root),'--manifest-sha256',a['MANIFEST'],'--final-sha256',a['FINAL'],'--report-sha256',a['REPORT']],capture_output=True,text=True)
before=observe(R);abefore=observe(A);baseline=read(C/'discovery-structural-r220-parent/observed-root.json');assert abefore==baseline
assert sha((R/'packet/verify_selection.py').read_bytes())=='eb402503abc9f27b9268ed1b356e765b51a70d184092f2b5487e4d6c94d2d994'
v=run(R,anchors);assert v.returncode==0,(v.stdout,v.stderr)
preserved=subprocess.run(['python3','-I','-B',str(Q/'verify_author_preserved.py')],capture_output=True,text=True);assert preserved.returncode==0,preserved.stderr
snap=read(Q/'author-before.json')
for e in snap['files']:
 z=baseline[e['path']];assert z['type']=='file' and all(z[k]==e[k] for k in ['bytes','sha256','mode'])
for e in snap['directories']:assert baseline[e['path']]['mode']==e['mode']
author=read(C/'discovery-structural-r220-parent/replay.json');m=read(R/'MANIFEST.json')
assert m['author_statement_sha256']==author['statement_sha256'] and m['author_proof_sha256']==author['proof_sha256']
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree={e['path']:e for e in json.loads(tb)['tree']}
auth=read(Q/'source-authentication.json');assert auth['authenticated_blob_count']==16
prefix='preprints/The-metric-Blaschke-theorem-September-23-2026'
assert auth['folder_entry']==tree[prefix]
blobs=0
for e in auth['entries']:
 assert e==tree[e['path']]
 if e['type']=='blob':
  b=(A/'packet/private/canonical'/Path(e['path']).relative_to(prefix)).read_bytes();assert len(b)==e['size'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha'];blobs+=1
logs=[json.loads(s) for s in (Q/'reads.jsonl').read_text().splitlines()];earlier=read(Q/'earlier-read-extents.json')['extents']
for e in logs+earlier:
 p=A/'packet'/e['path'];assert p.resolve().is_relative_to(A/'packet');b=p.read_bytes();lines=b.splitlines(keepends=True);lo,hi=e['bytes'];first,last=e['lines']
 assert lo==sum(map(len,lines[:first-1])) and hi==sum(map(len,lines[:last])) and sha(b[lo:hi])==e['sha256']
hist=read(Q/'history-selection.json');assert hist['path']=='frontier/experiments/i313_small_information_endpoint/analysis.md' and hist['bytes']==[6017,8385]
with (PROJECT/hist['path']).open('rb') as f:f.seek(6017);b=f.read(8385-6017)
assert sha(b)==hist['sha256']
pdfs=0
for e in read(A/'packet/private/primary/access.json'):
 if e['name'] in ['Kazdan1978','Berger1980','RovenskiiToponogov1996']:
  b=(A/'packet/private/primary'/(e['name']+'.pdf')).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'];pdfs+=1
e=read(A/'packet/private/primary/Boyd-access.json');b=(A/'packet/private/primary/BoydVandenberghe2004.pdf').read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256'];pdfs+=1
controls=[]
with tempfile.TemporaryDirectory(prefix='contribution-controls-',dir=P) as tmp:
 base=R/'controls';ca={'FINAL':sha((base/'packet/FINAL.md').read_bytes()),'MANIFEST':sha((base/'MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())}
 for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode','symlink']:
  dst=Path(tmp)/case;shutil.copytree(base,dst);a=dict(ca);f=dst/'packet/note.txt';pm=stat.S_IMODE((dst/'packet').stat().st_mode);(dst/'packet').chmod(pm|0o200)
  if case=='wrong-anchor':a['FINAL']='0'*64
  elif case=='changed-bytes':b=f.read_bytes();fm=stat.S_IMODE(f.stat().st_mode);f.chmod(fm|0o200);f.write_bytes(bytes([b[0]^1])+b[1:]);f.chmod(fm)
  elif case=='extra-file':(dst/'packet/extra.txt').write_text('extra\n')
  elif case=='missing-file':f.unlink()
  elif case=='file-mode':f.chmod(0o600 if stat.S_IMODE(f.stat().st_mode)!=0o600 else 0o644)
  elif case=='directory-mode':(dst/'packet').chmod(0o700 if stat.S_IMODE((dst/'packet').stat().st_mode)!=0o700 else 0o755)
  elif case=='symlink':f.unlink();f.symlink_to('FINAL.md')
  if case!='directory-mode':(dst/'packet').chmod(pm)
  q=run(dst,a);ok=q.returncode==0;assert ok==(case=='intact'),(case,q.stdout,q.stderr);controls.append({'case':case,'accepted':ok,'expected':case=='intact'})
assert observe(R)==before and observe(A)==abefore
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'review_files':sum(e['type']=='file' for e in before.values()),'review_directories':sum(e['type']=='directory' for e in before.values()),'review_originals_bytes_modes_unchanged':True,'author_preservation':json.loads(preserved.stdout),'author_baseline_files':sum(e['type']=='file' for e in baseline.values()),'author_baseline_directories':sum(e['type']=='directory' for e in baseline.values()),'all_author_baseline_bytes_modes_unchanged':True,'canonical_blob_bindings':blobs,'logged_extent_bindings':len(logs),'retrospective_earlier_extent_bindings':len(earlier),'primary_pdf_bindings':pdfs,'exact_original_history_span_bindings':1,'formal_navigation':read(Q/'reviewer-network-access.json'),'copied_controls':controls,'parent_read_recovery':'Initial combined tool output exceeded the outer output budget. REVIEW bytes[14000,24639) and the full LIMITS were reread untruncated, covering the missing middle with overlap. REPORT and FINAL were visible completely.','limits':'Parent read complete REVIEW/LIMITS/REPORT/FINAL and both verifiers. Canonical, primary, historical and logged underlying bodies identity-bound only; no inherited semantic reading. Review source coverage is scoped, primary OCR/crop/unread-dependency and adjacent-exposure limits remain. No exhaustive novelty or formal coverage claimed. Full correctness remains UNDISCHARGED; no correctness task polling or result inspection performed.'}
for name,value in [('contribution-replay.json',out),('contribution-observed-root.json',before)]:
 p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
