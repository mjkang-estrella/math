"""Read-only artifact verification; no mathematical grade."""
from pathlib import Path, PurePosixPath
import hashlib, json, stat, subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;R=D.parent/'fresh-arithmetic-discovery-r162cp'
A={'FINAL.md':'2f791c7cd05535ae785f24de83854dcd3e6a453f6548ba1610dc52ba77f6cffb','MANIFEST.json':'940a69a40a640e675e676a4decca6f3b8f4d6c07019dce49c4e8036c55342d5b','REPORT.md':'33693b6e6765e9129082f730e177d08c55cc9d3526c9863b7754827a33300484'}
def sha(a):return hashlib.sha256(a).hexdigest()
def unique(pairs):
 d={}
 for k,v in pairs:assert k not in d;d[k]=v
 return d
def read(p):return json.loads(p.read_bytes(),object_pairs_hook=unique)
def snap(root):
 out={}
 for p in root.rglob('*'):
  s=p.lstat();assert not stat.S_ISLNK(s.st_mode)
  if stat.S_ISREG(s.st_mode):
   a=p.read_bytes();out[p.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=s.st_mode)
  else:assert stat.S_ISDIR(s.st_mode)
 return out
before=read(D/'private/intake/root-before.json');assert snap(R)==before
for n,h in A.items():assert before[n]['sha256']==h and before[n]['mode']==33188
args=['--root',str(R),'--project',str(P)]
for k,v in zip(['final-sha256','manifest-sha256','report-sha256'],A.values()):args+=['--'+k,v]
vp=R/'verify_packet.py';run=subprocess.run(['python3','-I','-B',str(vp),*args],cwd=P,text=True,capture_output=True);assert run.returncode==0,(run.stdout,run.stderr)
m=read(R/'MANIFEST.json');names=[e['path'] for e in m['files']];assert names==sorted(set(names)) and len({n.casefold() for n in names})==len(names)
assert set(before)==set(names)|{'MANIFEST.json','REPORT.md'}
for e in m['files']:
 q=PurePosixPath(e['path']);assert not q.is_absolute() and '..' not in q.parts and str(q)==e['path'] and '\\' not in e['path']
 p=R/e['path'];s=p.lstat();a=p.read_bytes();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1 and len(a)==e['bytes'] and sha(a)==e['sha256'] and s.st_mode==e['mode']
dirs={'.':R.stat().st_mode};dirs.update({p.relative_to(R).as_posix():p.stat().st_mode for p in R.rglob('*') if p.is_dir()});assert dirs=={e['path']:e['mode'] for e in m['directories']}
raw=(P/'sources/preprints-tree.json').read_bytes();assert len(raw)==4858136 and sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=read(P/'sources/preprints-tree.json');assert tree['truncated'] is False;by={e['path']:e for e in tree['tree']};selected=read(R/'private/source/tree.json');assert len(selected)==15
blobs=trees=0
for e in selected:
 assert by[e['path']]==e
 if e['type']=='blob':
  a=(R/'private/source'/e['path'].split('Bounded-degree-coboundary-expanders-in-every-dimension-September-24-2026/',1)[1]).read_bytes();assert len(a)==e['size'] and hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['sha'];blobs+=1
 else:
  assert e['type']=='tree';children=[x for x in selected if str(PurePosixPath(x['path']).parent)==e['path']];children.sort(key=lambda x:(PurePosixPath(x['path']).name+('/' if x['type']=='tree' else '')).encode())
  a=b''.join((x['mode'].lstrip('0')+' '+PurePosixPath(x['path']).name).encode()+b'\0'+bytes.fromhex(x['sha']) for x in children);assert hashlib.sha1(b'tree '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['sha'];trees+=1
primary=read(R/'private/primary/bindings.json');assert len(primary)==6
primary += [dict(name=n,**read(R/('private/primary/'+n+'-binding.json'))) for n in ['LA','LAv2']]
assert len(primary)==len({e['name'] for e in primary})==8
for e in primary:
 a=(R/'private/primary'/(e['name']+'.pdf')).read_bytes();assert a.startswith(b'%PDF') and len(a)==e['bytes'] and sha(a)==e['sha256']
assert blobs==10 and trees==5
controls=[]
for i,n in enumerate(A):
 bad=args.copy();bad[5+2*i]='0'*64;test=subprocess.run(['python3','-I','-B',str(vp),*bad],cwd=P,text=True,capture_output=True);assert test.returncode!=0 and 'anchor' in test.stderr;controls.append(n+' wrong anchor rejected')
assert snap(R)==before
assert before['STATEMENT.md']['sha256']=='ebbecfde0342e866f1401764980ccaf1f3f0c08bc1aea5269e217021774594c9'
assert before['PROOF.md']['sha256']=='7331535f72a9c9dbab2da0396af34c78eb0a1065afb5e96d4cfc618a22a052b6'
out=dict(status='MATCH',mathematical_grade=False,bundled_verifier=run.stdout.strip(),payloads=len(names),payload_bytes=sum(e['bytes'] for e in m['files']),whole_files=len(before),directories=len(dirs),anchors=A,author_bytes_and_modes_unchanged=True,source_blobs=blobs,source_trees_independently_verified=trees,primary_pdf_bindings=len(primary),completed_originals_and_copies=5,controls=controls,recorded_author_controls=read(R/'private/controls/RESULTS.json'))
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
