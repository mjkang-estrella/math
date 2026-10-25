from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;R=D.parent/'fresh-arithmetic-discovery-r162cr'
A={'FINAL.md':'9c241a99803dc252c6fdd037af4c2b844d4ac3843d53e873ddca9658c4bcc96b','MANIFEST.json':'bc050c107c4de48b6a3a4349b3cd2d16eec303312c1a89669fc59164bd75c105','REPORT.md':'041df1e79bc629632fd6be20a8f310e6008085c358102587bfc1aa3e67316d21'}
def sha(a):return hashlib.sha256(a).hexdigest()
def unique(pairs):
 d={}
 for k,v in pairs:assert k not in d;d[k]=v
 return d
def read(p):return json.loads(p.read_bytes(),object_pairs_hook=unique)
def snap(root):
 d={}
 for p in root.rglob('*'):
  s=p.lstat();assert not stat.S_ISLNK(s.st_mode)
  if stat.S_ISREG(s.st_mode):
   a=p.read_bytes();d[p.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=s.st_mode)
  else:assert stat.S_ISDIR(s.st_mode)
 return d
before=read(D/'private/intake/root-before.json');assert snap(R)==before
for n,h in A.items():assert before[n]['sha256']==h
args=['--root',str(R),'--project-root',str(P)]
for n,h in zip(['final-sha256','manifest-sha256','report-sha256'],A.values()):args+=['--'+n,h]
vp=R/'verify.py';r=subprocess.run(['python3','-I','-B',str(vp),*args],cwd=P,text=True,capture_output=True);assert r.returncode==0,(r.stdout,r.stderr)
m=read(R/'MANIFEST.json');files=m['files'];ds=m['directories'];names=[x['path'] for x in files]
assert names==sorted(set(names)) and len({n.casefold() for n in names})==len(names) and set(before)==set(names)|{'MANIFEST.json','REPORT.md'}
for e in files:
 q=PurePosixPath(e['path']);assert not q.is_absolute() and '..' not in q.parts and str(q)==e['path'] and '\\' not in e['path']
 p=R/e['path'];a=p.read_bytes();s=p.lstat();assert s.st_nlink==1 and len(a)==e['bytes'] and sha(a)==e['sha256'] and s.st_mode==e['full_mode']
dirs={'.':R.stat().st_mode};dirs.update({p.relative_to(R).as_posix():p.stat().st_mode for p in R.rglob('*') if p.is_dir()});assert dirs=={e['path']:e['full_mode'] for e in ds}
raw=(P/'sources/preprints-tree.json').read_bytes();assert len(raw)==4858136 and sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
master=read(P/'sources/preprints-tree.json');assert master['truncated'] is False;by={e['path']:e for e in master['tree']};tree=read(R/'private/source-tree.json');assert len(tree)==13
blobs=trees=0
for e in tree:
 assert by[e['path']]==e
 if e['type']=='blob':
  a=(R/'private/source'/e['path'].split('The-circulant-Hadamard-conjecture-September-23-2026/',1)[1]).read_bytes();assert len(a)==e['size'] and hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['sha'];blobs+=1
 else:
  assert e['type']=='tree';ch=[x for x in tree if str(PurePosixPath(x['path']).parent)==e['path']];ch.sort(key=lambda x:(PurePosixPath(x['path']).name+('/' if x['type']=='tree' else '')).encode());a=b''.join((x['mode'].lstrip('0')+' '+PurePosixPath(x['path']).name).encode()+b'\0'+bytes.fromhex(x['sha']) for x in ch);assert hashlib.sha1(b'tree '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['sha'];trees+=1
primary=read(R/'private/primary/bindings.json');assert len(primary)==8
for e in primary:
 a=(R/e['pdf']).read_bytes();assert a.startswith(b'%PDF') and len(a)==e['bytes'] and sha(a)==e['sha256']
assert blobs==10 and trees==3
controls=[]
for i,n in enumerate(A):
 bad=args.copy();bad[5+2*i]='0'*64;t=subprocess.run(['python3','-I','-B',str(vp),*bad],cwd=P,text=True,capture_output=True);assert t.returncode!=0 and 'anchor mismatch' in (t.stdout+t.stderr);controls.append(n+' rejected')
assert snap(R)==before
out=dict(status='MATCH',mathematical_grade=False,bundled_verifier=r.stdout.strip(),payloads=len(files),payload_bytes=sum(e['bytes'] for e in files),whole_files=len(before),directories=len(dirs),anchors=A,author_bytes_and_modes_unchanged=True,source_blobs=blobs,source_trees_independently_verified=trees,primary_pdf_bindings=len(primary),completed_originals_and_copies=5,controls=controls)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
