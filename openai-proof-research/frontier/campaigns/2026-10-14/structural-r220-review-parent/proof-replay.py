#!/usr/bin/env python3
"""Read-only correctness packet replay; integrity is separate from mathematics."""
from pathlib import Path
import datetime,hashlib,json,os,shutil,stat,subprocess,tempfile
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2];R=C/'structural-r220-proof-r1';Q=R/'packet/private';A=C/'fresh-structural-discovery-r220'
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
anchors={'FINAL':'629c3618e1b03a12ab4cfabc65cb9edfd29f05f74ea1edcc46e6a5fa8e7906ec','MANIFEST':'61c39367d04a4448dbb0c4622b0b42d515f485568955f885b4097cf161629405','REPORT':'8c75ca9548db0c1e7aef77304f6db6cc0183774f904b0c92f96a7302ade44d36'}
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
 return subprocess.run(['python3','-I','-B',str(R/'packet/verify_packet.py'),'--root',str(root),'--manifest-sha256',a['MANIFEST'],'--final-sha256',a['FINAL'],'--report-sha256',a['REPORT']],capture_output=True,text=True)
before=observe(R);abefore=observe(A);baseline=read(C/'discovery-structural-r220-parent/observed-root.json');assert abefore==baseline
assert sha((R/'packet/verify_packet.py').read_bytes())=='6c8a0c6f426103afc1cda6e06e155cf0e0d3f4f3ece1a540de115270cdd8a627'
v=run(R,anchors);assert v.returncode==0,(v.stdout,v.stderr)
snap=read(Q/'author-before.json');nf=nd=0
for path,e in snap.items():
 rel=(PROJECT/path).relative_to(A).as_posix();z=baseline[rel]
 assert all(z[k]==e[k] for k in e)
 if e.get('type')=='directory':nd+=1
 else:nf+=1
assert (nf,nd)==(70,9)
after=read(Q/'author-after.json');assert after['before_snapshot_sha256']==after['after_canonical_snapshot_sha256']==sha((Q/'author-before.json').read_bytes())
author=read(C/'discovery-structural-r220-parent/replay.json');m=read(R/'MANIFEST.json');assert m['statement_sha256']==author['statement_sha256'] and m['proof_sha256']==author['proof_sha256']
tb=(PROJECT/'sources/preprints-tree.json').read_bytes();assert sha(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';tree={e['path']:e for e in json.loads(tb)['tree']}
auth=read(Q/'source-authentication.json');prefix='preprints/The-metric-Blaschke-theorem-September-23-2026';blobs=0
for e in auth['selected']:
 assert e==tree[e['path']]
 if e['type']=='blob':
  b=(A/'packet/private/canonical'/Path(e['path']).relative_to(prefix)).read_bytes();assert len(b)==e['size'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha'];blobs+=1
assert blobs==16
logs=[json.loads(s) for s in (Q/'reads.jsonl').read_text().splitlines()];bindings=[]
for e in logs:
 p=PROJECT/e['path'];assert p.is_relative_to(A/'packet');b=p.read_bytes();assert sha(b)==e['sha256'];lines=b.split(b'\n');first,last=e['lines'];lo,hi=e['bytes']
 assert lo==sum(len(x)+1 for x in lines[:first-1]) and hi==sum(len(x)+1 for x in lines[:last-1])+len(lines[last-1])
 bindings.append(dict(path=e['path'],bytes=[lo,hi],selection_sha256=sha(b[lo:hi]),whole_file_sha256=e['sha256']))
for filename,expected in [('Kazdan1978.pdf','c19ea3394808b54013d24c3137d36a49320a9a672f2d141a846144a9f181b227'),('BoydVandenberghe2004.pdf','40d976c83c18cce1900eff8c41bd5ad408c102b813af39d05ff85678ccf8d76e')]:assert sha((A/'packet/private/primary'/filename).read_bytes())==expected
controls=[]
with tempfile.TemporaryDirectory(prefix='proof-controls-',dir=P) as tmp:
 base=Path(tmp)/'base';base.mkdir(mode=0o700);packet=base/'packet';packet.mkdir()
 for name,body in [('FINAL.md',b'tiny final\n'),('note.txt',b'tiny note\n')]:p=packet/name;p.write_bytes(body);p.chmod(0o444)
 packet.chmod(0o555);(base/'REPORT.md').write_bytes(b'tiny report\n');(base/'REPORT.md').chmod(0o400)
 fs=[];ds=[]
 for path,e in observe(packet).items():
  if e['type']=='file':fs.append(dict(path=path,**{k:e[k] for k in ['bytes','mode','sha256']}))
  else:ds.append(dict(path=path,mode=e['mode']))
 (base/'MANIFEST.json').write_text(json.dumps({'format':'structural-r220-correctness-r1-exact-selection-v1','files':sorted(fs,key=lambda e:e['path']),'directories':sorted(ds,key=lambda e:e['path'])},indent=2)+'\n');(base/'MANIFEST.json').chmod(0o400)
 ca={'FINAL':sha((packet/'FINAL.md').read_bytes()),'MANIFEST':sha((base/'MANIFEST.json').read_bytes()),'REPORT':sha((base/'REPORT.md').read_bytes())}
 for case in ['intact','wrong-anchor','changed-bytes','extra-file','missing-file','file-mode','directory-mode','symlink']:
  dst=Path(tmp)/case;shutil.copytree(base,dst);a=dict(ca);f=dst/'packet/note.txt';(dst/'packet').chmod(0o755)
  if case=='wrong-anchor':a['FINAL']='0'*64
  elif case=='changed-bytes':b=f.read_bytes();f.chmod(0o644);f.write_bytes(bytes([b[0]^1])+b[1:]);f.chmod(0o444)
  elif case=='extra-file':(dst/'packet/extra.txt').write_text('extra\n')
  elif case=='missing-file':f.unlink()
  elif case=='file-mode':f.chmod(0o400)
  elif case=='symlink':f.unlink();f.symlink_to('FINAL.md')
  if case!='directory-mode':(dst/'packet').chmod(0o555)
  q=run(dst,a);ok=q.returncode==0;assert ok==(case=='intact'),(case,q.stdout,q.stderr);controls.append({'case':case,'accepted':ok,'expected':case=='intact'})
assert observe(R)==before and observe(A)==abefore
out={'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_only':True,'anchors':anchors,'verification':json.loads(v.stdout),'review_files':sum(e['type']=='file' for e in before.values()),'review_directories':sum(e['type']=='directory' for e in before.values()),'review_originals_bytes_modes_unchanged':True,'admitted_author_files':nf,'admitted_author_directories':nd,'author_baseline_files':140,'author_baseline_directories':17,'all_author_baseline_bytes_modes_unchanged':True,'canonical_blob_bindings':blobs,'LF_extent_bindings':len(logs),'primary_pdf_bindings':2,'formal_navigation':read(Q/'lean-access.json'),'copied_controls':controls,'limits':'Parent read complete REVIEW/READING-LIMITS/REPORT/FINAL, verifiers and working findings. Underlying canonical/primary and logged bodies identity-bound without inherited semantic reading. Whole-file hashes and exact LF line/byte coordinates were bound; parent-computed extent hashes are private. No original-history body selected by reviewer. Nonsemantic metadata key-list output was clipped; required schemas were read and exact records bound programmatically. Both helper scripts that write to original paths were inspected but not executed. No formal support or exhaustive history clearance.'}
for name,value in [('proof-replay.json',out),('proof-observed-root.json',before),('proof-read-bindings.json',bindings)]:
 p=P/name;p.write_text(json.dumps(value,indent=2)+'\n');p.chmod(0o600)
print(json.dumps(out,indent=2))
