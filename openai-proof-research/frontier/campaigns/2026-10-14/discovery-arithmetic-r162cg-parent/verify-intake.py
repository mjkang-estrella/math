#!/usr/bin/env python3
"""Read-only sealed-packet verification, not a mathematical review."""
from pathlib import Path, PurePosixPath
import hashlib, json, stat, subprocess
P=Path(__file__).resolve().parents[4]; D=Path(__file__).resolve().parent
R=D.parent/'fresh-arithmetic-discovery-r162cg'
A={'FINAL.md':'488dfe6c6b63f2ad0bc00c2a1c0872f1b38e979b0e2e36af6e1580542f9e145f','MANIFEST.json':'aa64059045eeae58a7dc58a03c24049b9d5c40cd9f0c7dab488998e063215d01','REPORT.md':'3497862ba5ca19b17b282b0a4d98ec78ed3a0189be687d9ab115b54cbabc1233'}
def sha(x): return hashlib.sha256(x).hexdigest()
def unique(xs):
 d={}
 for k,v in xs: assert k not in d; d[k]=v
 return d
def read(p): return json.loads(p.read_bytes(),object_pairs_hook=unique)
def snap(root):
 d={}
 for p in root.rglob('*'):
  s=p.lstat(); assert not stat.S_ISLNK(s.st_mode)
  if stat.S_ISREG(s.st_mode):
   a=p.read_bytes();d[p.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=s.st_mode)
  else: assert stat.S_ISDIR(s.st_mode)
 return d
before=read(D/'private/intake/root-before.json'); assert snap(R)==before
for n,a in A.items(): assert before[n]['sha256']==a and before[n]['mode']==33188
args=['--root',str(R)]
for n,k in zip(A,['final-sha256','manifest-sha256','report-sha256']):args.extend(['--'+k,A[n]])
vp=R/'private/verify.py'
run=subprocess.run(['python3','-I','-B',str(vp),*args],cwd=P,capture_output=True,text=True)
assert run.returncode==0,(run.stdout,run.stderr)
m=read(R/'MANIFEST.json');names=[e['path'] for e in m['files']]
assert names==sorted(set(names)) and len({n.casefold() for n in names})==len(names)
assert set(before)==set(names)|{'MANIFEST.json','REPORT.md'}
for e in m['files']:
 q=PurePosixPath(e['path']); assert not q.is_absolute() and '..' not in q.parts and str(q)==e['path'] and '\\' not in e['path']
 p=R/e['path'];s=p.lstat();a=p.read_bytes()
 assert stat.S_ISREG(s.st_mode) and s.st_nlink==1 and len(a)==e['size'] and sha(a)==e['sha256'] and s.st_mode==e['mode']
dirs={'.':R.stat().st_mode};dirs.update({p.relative_to(R).as_posix():p.stat().st_mode for p in R.rglob('*') if p.is_dir()})
assert dirs=={e['path']:e['mode'] for e in m['directories']}
raw=(P/'sources/preprints-tree.json').read_bytes()
assert len(raw)==4858136 and sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=read(P/'sources/preprints-tree.json'); assert tree['truncated'] is False
by={e['path']:e for e in tree['tree']};selected=read(R/'private/canonical-bindings.json')
for e in selected:
 for k in ['path','mode','type','sha']:assert by[e['path']][k]==e[k]
blobs=0;trees=0
for e in selected:
 if e['type']=='blob':
  a=(R/e['local']).read_bytes(); assert len(a)==e['size']
  assert hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['sha'];blobs+=1
 else:
  assert e['type']=='tree'
  children=[x for x in selected if str(PurePosixPath(x['path']).parent)==e['path']]
  children.sort(key=lambda x:(PurePosixPath(x['path']).name+('/' if x['type']=='tree' else '')).encode())
  a=b''.join((x['mode'].lstrip('0')+' '+PurePosixPath(x['path']).name).encode()+b'\0'+bytes.fromhex(x['sha']) for x in children)
  assert hashlib.sha1(b'tree '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['sha'];trees+=1
primary=[]
for n in ['acquisition.json','acquisition2.json','acquisition3.json','acquisition4.json']:
 primary.extend(e for e in read(R/'private/primary'/n) if 'error' not in e)
assert len(primary)==len({e['id'] for e in primary})==9
for e in primary:
 a=(R/('private/primary/'+e['id']+'.pdf')).read_bytes()
 assert a.startswith(b'%PDF') and len(a)==e['size'] and sha(a)==e['sha256']
assert blobs==11 and trees==3
controls=[]
for i,n in enumerate(A):
 bad=args.copy();bad[3+2*i]='0'*64
 test=subprocess.run(['python3','-I','-B',str(vp),*bad],cwd=P,capture_output=True,text=True)
 assert test.returncode!=0 and 'anchor mismatch' in test.stderr and n in test.stderr;controls.append(n+' wrong anchor rejected')
assert snap(R)==before
out=dict(status='MATCH',mathematical_grade=False,bundled_verifier=run.stdout.strip(),payloads=len(names),payload_bytes=sum(e['size'] for e in m['files']),whole_files=len(before),directories=len(dirs),anchors=A,author_bytes_and_modes_unchanged=True,source_blobs=blobs,source_trees_independently_verified=trees,primary_pdf_bindings=len(primary),completed_originals_and_copies=5,controls=controls,recorded_author_controls=read(R/'private/control-results.json'))
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
