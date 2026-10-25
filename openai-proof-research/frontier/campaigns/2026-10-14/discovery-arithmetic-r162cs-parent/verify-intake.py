from pathlib import Path, PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;R=D.parent/'fresh-arithmetic-discovery-r162cs'
A={'FINAL.md':'4861f60980c102dfe8c7f4adf7f409a0aae1435a27cedb6917559a7f25cc4a92','MANIFEST.json':'cec2b629096509e054a4825fe2711361a8fdd3a6dd3eb5a4991f54e286e2fe87','REPORT.md':'aaa869bb7e27caa7af4427eb660ba8ec43759a67cb6c6a958869a0544cf8e1d6'}
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
args=['--root',str(R),'--project',str(P)]
for n,h in zip(['final-sha','manifest-sha','report-sha'],A.values()):args+=['--'+n,h]
vp=R/'verify.py';r=subprocess.run(['python3','-I','-B',str(vp),*args],cwd=P,text=True,capture_output=True);assert r.returncode==0,(r.stdout,r.stderr)
m=read(R/'MANIFEST.json');files=m['files'];names=[e['path'] for e in files]
assert names==sorted(set(names)) and len({n.casefold() for n in names})==len(names) and set(before)==set(names)|{'MANIFEST.json','REPORT.md'}
for e in files:
 q=PurePosixPath(e['path']);assert not q.is_absolute() and '..' not in q.parts and str(q)==e['path'] and '\\' not in e['path']
 p=R/e['path'];a=p.read_bytes();s=p.lstat();assert s.st_nlink==1 and len(a)==e['bytes'] and sha(a)==e['sha256'] and s.st_mode==e['mode']
dirs={p.relative_to(R).as_posix():p.stat().st_mode for p in R.rglob('*') if p.is_dir()};assert R.stat().st_mode==m['root_mode'] and dirs=={e['path']:e['mode'] for e in m['directories']}
for n in ['MANIFEST.json','REPORT.md']:assert (R/n).stat().st_mode==m['detached_modes'][n]
raw=(P/'sources/preprints-tree.json').read_bytes();assert len(raw)==4858136 and sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
master=read(P/'sources/preprints-tree.json');assert master['truncated'] is False;by={e['path']:e for e in master['tree']};tree=read(R/'private/source-tree.json');assert len(tree)==7
bindings=read(R/'private/bindings.json');by_binding={e['path']:e for e in bindings};blobs=trees=originals=0
for e in tree:
 assert by[e['path']]==e
 if e['type']=='blob':
  rec=by_binding[e['path']];a=(R/rec['copy']).read_bytes();assert len(a)==e['size'] and sha(a)==rec['sha256'] and hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['sha'];blobs+=1
 else:
  assert e['type']=='tree';ch=[x for x in tree if str(PurePosixPath(x['path']).parent)==e['path']];ch.sort(key=lambda x:(PurePosixPath(x['path']).name+('/' if x['type']=='tree' else '')).encode());a=b''.join((x['mode'].lstrip('0')+' '+PurePosixPath(x['path']).name).encode()+b'\0'+bytes.fromhex(x['sha']) for x in ch);assert hashlib.sha1(b'tree '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['sha'];trees+=1
for e in bindings:
 if 'git_blob' in e:continue
 p=P/e['path'];c=R/e['copy'];a=p.read_bytes();assert a==c.read_bytes() and len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==c.stat().st_mode==e['mode'];originals+=1
primary=read(R/'private/primary/reading.json')
for e in primary['files']:
 a=(R/e['path']).read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256']
assert blobs==5 and trees==2 and originals==5
controls=[]
for i,n in enumerate(A):
 bad=args.copy();bad[5+2*i]='0'*64;t=subprocess.run(['python3','-I','-B',str(vp),*bad],cwd=P,text=True,capture_output=True);assert t.returncode!=0 and 'anchor mismatch' in (t.stdout+t.stderr);controls.append(n+' rejected')
assert snap(R)==before
out=dict(status='MATCH',mathematical_grade=False,bundled_verifier=json.loads(r.stdout),payloads=len(files),payload_bytes=sum(e['bytes'] for e in files),whole_files=len(before),directories=len(dirs)+1,anchors=A,author_bytes_and_modes_unchanged=True,source_blobs=blobs,source_trees_independently_verified=trees,primary_file_bindings=len(primary['files']),primary_pdfs=len(primary['papers']),completed_originals_and_copies=originals,controls=controls)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
