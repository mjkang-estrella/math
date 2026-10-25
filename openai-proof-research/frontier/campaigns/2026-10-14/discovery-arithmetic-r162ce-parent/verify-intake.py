#!/usr/bin/env python3
"""Read-only sealed-packet verification, not a mathematical review."""
from pathlib import Path, PurePosixPath
import hashlib, json, stat, subprocess
P=Path(__file__).resolve().parents[4]; D=Path(__file__).resolve().parent
R=D.parent/'fresh-arithmetic-discovery-r162ce'
A={'FINAL.md':'b4be8233faaa7b2e4682624701226c6753c71e9983b1a3ce564640ea7704f230','MANIFEST.json':'6a86ea1225533c1a241f98affe3fd7389f7d72f623c283323aec5c3ba454736d','REPORT.md':'7e2d9ab55f618275ec0f20f7d2584b52db6fdce8af17c3a1e71c867ac197769d'}
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
 assert stat.S_ISREG(s.st_mode) and s.st_nlink==1 and len(a)==e['bytes'] and sha(a)==e['sha256'] and s.st_mode==e['full_mode']
dirs={'.':R.stat().st_mode};dirs.update({p.relative_to(R).as_posix():p.stat().st_mode for p in R.rglob('*') if p.is_dir()})
assert dirs=={e['path']:e['full_mode'] for e in m['directories']}
raw=(P/'sources/preprints-tree.json').read_bytes()
assert len(raw)==4858136 and sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=read(P/'sources/preprints-tree.json'); assert tree['truncated'] is False
by={e['path']:e for e in tree['tree']};selected=read(R/'private/tree-selection.json')
for e in selected: assert by[e['path']]==e
blobs=0;trees=0
for e in selected:
 if e['type']=='blob':
  a=(R/'private/source'/e['path'].split('The-higher-dimensional-Erdos-distinct-distances-conjecture-September-23-2026/',1)[1]).read_bytes(); assert len(a)==e['size']
  assert hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['sha'];blobs+=1
 else:
  assert e['type']=='tree'
  children=[x for x in selected if str(PurePosixPath(x['path']).parent)==e['path']]
  children.sort(key=lambda x:(PurePosixPath(x['path']).name+('/' if x['type']=='tree' else '')).encode())
  a=b''.join((x['mode'].lstrip('0')+' '+PurePosixPath(x['path']).name).encode()+b'\0'+bytes.fromhex(x['sha']) for x in children)
  assert hashlib.sha1(b'tree '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['sha'];trees+=1
primary=[]
for n in ['acquisitions.json','acquisitions-extra.json']:
 for e in read(R/'private/primary'/n):
  if e.get('status')=='downloaded': primary.append((e['name'],e))
primary.extend((n,read(R/'private/primary'/f)) for n,f in [('APST','APST-acquisition.json'),('APST-long','APST-long-acquisition.json')])
assert len({n for n,e in primary})==len(primary)==5
for n,e in primary:
 a=(R/('private/primary/'+n+'.pdf')).read_bytes()
 assert a.startswith(b'%PDF') and len(a)==e.get('size',e.get('bytes')) and sha(a)==e['sha256']
assert blobs==19 and trees==4
controls=[]
for i,n in enumerate(A):
 bad=args.copy();bad[3+2*i]='0'*64
 test=subprocess.run(['python3','-I','-B',str(vp),*bad],cwd=P,capture_output=True,text=True)
 assert test.returncode!=0 and 'detached anchor: '+n in test.stderr;controls.append(n+' wrong anchor rejected')
assert snap(R)==before
out=dict(status='MATCH',mathematical_grade=False,bundled_verifier=run.stdout.strip(),payloads=len(names),payload_bytes=sum(e['bytes'] for e in m['files']),whole_files=len(before),directories=len(dirs),anchors=A,author_bytes_and_modes_unchanged=True,source_blobs=blobs,source_trees_independently_verified=trees,primary_pdf_bindings=len(primary),completed_originals_and_copies=5,controls=controls,recorded_author_controls=read(R/'private/control-results.json'))
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
