#!/usr/bin/env python3
"""Read-only contribution artifact check; correctness remains unassigned."""
from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
R=B/'arithmetic-r162cb-proof-r1';A={'FINAL.md':'1ae6d610c554e828a390852a260c08118426d1a8d97fd4a04f9a282b06a59252','MANIFEST.json':'4d45c82de69defb51c7e96fa0b27a09f32407e11c8446a62fe784bb3a7240266','REPORT.md':'a35621af011f3ef7489253459026376cf344f26222d4e9a1cb7e7d850e8d8ffe'}
def sha(a):return hashlib.sha256(a).hexdigest()
def unique(xs):
 d={}
 for k,v in xs:assert k not in d;d[k]=v
 return d
def read(p):return json.loads(p.read_bytes(),object_pairs_hook=unique)
def snap(root):
 out={}
 for p in root.rglob('*'):
  s=p.lstat();assert not stat.S_ISLNK(s.st_mode)
  if stat.S_ISREG(s.st_mode):a=p.read_bytes();out[p.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=s.st_mode)
  else:assert stat.S_ISDIR(s.st_mode)
 return out
before=read(D/'private/root-before.json');assert snap(R)==before
for n,h in A.items():assert before[n]['sha256']==h
vp=R/'verify.py';args=[]
for n,k,sz in zip(A,['final','manifest','report'],[6861,13875,2123]):args.extend(['--'+k,A[n]+':'+str(sz)+':33188'])
args.append('--check-author')
run=subprocess.run(['python','-I','-B',str(vp),*args],cwd=P,capture_output=True,text=True);assert run.returncode==0,(run.stdout,run.stderr)
m=read(R/'MANIFEST.json');records=m['files'];names=[e['path'] for e in records]
assert names==sorted(set(names)) and len({n.casefold() for n in names})==len(names)
assert set(before)==set(names)|{'MANIFEST.json','REPORT.md'}
for e in records:
 q=PurePosixPath(e['path']);assert not q.is_absolute() and '..' not in q.parts and str(q)==e['path'] and '\\' not in e['path']
 p=R/e['path'];a=p.read_bytes();s=p.lstat();assert s.st_nlink==1 and stat.S_ISREG(s.st_mode)
 assert len(a)==e['bytes'] and sha(a)==e['sha256'] and s.st_mode==e['mode']
dirs={'.':R.stat().st_mode};dirs.update({p.relative_to(R).as_posix():p.stat().st_mode for p in R.rglob('*') if p.is_dir()})
assert dirs=={e['path']:e['mode'] for e in m['directories']}
author=B/'fresh-arithmetic-discovery-r162cb';author_before=read(B/'discovery-arithmetic-r162cb-parent/private/intake/root-before.json')
assert len(author_before)==61 and snap(author)==author_before
controls=[]
for i,n in enumerate(A):
 bad=args.copy();bad[1+2*i]='0'*64+':'+str([6861,13875,2123][i])+':33188'
 test=subprocess.run(['python','-I','-B',str(vp),*bad],cwd=P,capture_output=True,text=True)
 assert test.returncode!=0 and 'detached anchor mismatch: '+n in test.stderr;controls.append(n+' wrong anchor rejected')
assert snap(R)==before and snap(author)==author_before
out=dict(status='MATCH',mathematical_grade=False,bundled_verifier=run.stdout.strip(),payloads=len(names),payload_bytes=sum(e['bytes'] for e in records),whole_files=len(before),directories=len(dirs),anchors=A,author_files_unchanged=61,review_bytes_and_modes_unchanged=True,wrong_anchor_controls=controls)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
