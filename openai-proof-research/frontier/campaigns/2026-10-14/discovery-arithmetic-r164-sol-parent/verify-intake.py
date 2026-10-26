from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;R=D.parent/'fresh-arithmetic-discovery-r164-sol'
A={'FINAL.md':'f6e4d1092ab43baa2a84ec971f9f70b5853e88a93a57b8d68e4ec4c94ffeaa25','MANIFEST.json':'7eb232822159fdbc129e09fc37193be50b7e1e40181ea4aa342f7460be684223','REPORT.md':'02be93b9fe57ac0f209ebdb45245cbf0577096077a99fae90e78ba9985af59d0'}
def sha(a):return hashlib.sha256(a).hexdigest()
def unique(pairs):
 d={}
 for k,v in pairs:assert k not in d;d[k]=v
 return d
def read(p):return json.loads(p.read_bytes(),object_pairs_hook=unique)
def snap():
 out={}
 for p in R.rglob('*'):
  s=p.lstat();assert not stat.S_ISLNK(s.st_mode)
  if stat.S_ISREG(s.st_mode):
   a=p.read_bytes();out[p.relative_to(R).as_posix()]={'bytes':len(a),'sha256':sha(a),'mode':s.st_mode}
  else:assert stat.S_ISDIR(s.st_mode)
 return out
before=read(D/'private/intake/root-before.json');assert snap()==before
for n,h in A.items():assert before[n]['sha256']==h
args=['--root',str(R),'--project',str(P)]
for label,h in zip(['final','manifest','report'],A.values()):args+=['--'+label+'-sha256',h]
run=subprocess.run(['python3','-I','-B',str(R/'verify.py'),*args],cwd=P,text=True,capture_output=True);assert run.returncode==0,(run.stdout,run.stderr)
m=read(R/'MANIFEST.json');names=[e['path'] for e in m['files']];assert names==sorted(set(names)) and len({n.casefold() for n in names})==len(names);assert set(before)==set(names)|set(A)|{'ANCHORS.json'}
for e in m['files']:
 q=PurePosixPath(e['path']);assert not q.is_absolute() and '..' not in q.parts and str(q)==e['path'] and '\\' not in e['path']
 p=R/e['path'];a=p.read_bytes();assert p.stat().st_nlink==1 and len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
dirs={'.':R.stat().st_mode};dirs.update({p.relative_to(R).as_posix():p.stat().st_mode for p in R.rglob('*') if p.is_dir()});assert dirs=={e['path']:e['mode'] for e in m['directories']};assert read(R/'ANCHORS.json')==A
raw=(P/'sources/preprints-tree.json').read_bytes();assert len(raw)==4858136 and sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b';master=json.loads(raw);assert not master['truncated'];by={e['path']:e for e in master['tree']};rows=read(R/'private/SOURCE-BINDINGS.json');assert len(rows)==32
blobs=trees=0
for e in rows:
 source=by[e['path']];assert all(e[k]==v for k,v in source.items())
 if e['type']=='blob':
  a=(R/e['local']).read_bytes();assert len(a)==e['size'] and sha(a)==e['sha256'] and hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['sha'];blobs+=1
 else:
  kids=[x for x in rows if str(PurePosixPath(x['path']).parent)==e['path']];kids.sort(key=lambda x:(PurePosixPath(x['path']).name+('/' if x['type']=='tree' else '')).encode());a=b''.join((x['mode'].lstrip('0')+' '+PurePosixPath(x['path']).name).encode()+b'\0'+bytes.fromhex(x['sha']) for x in kids);assert hashlib.sha1(b'tree '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['sha'];trees+=1
copies=read(R/'private/completed-bindings.json');assert len(copies)==5
for e in copies:
 p=P/e['path'];q=R/e['copy'];a=p.read_bytes();assert a==q.read_bytes() and len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==q.stat().st_mode==e['mode']
primary=read(R/'private/primary/access.json')+read(R/'private/primary/packing-access.json')+[dict(read(R/'private/primary/planar-access.json'),name='planar')];assert len(primary)==8
for e in primary:
 a=(R/'private/primary'/(e['name']+'.pdf')).read_bytes();assert a.startswith(b'%PDF') and len(a)==e['bytes'] and sha(a)==e['sha256']
controls=[]
for i,n in enumerate(A):
 bad=args.copy();bad[5+2*i]='0'*64;r=subprocess.run(['python3','-I','-B',str(R/'verify.py'),*bad],cwd=P,text=True,capture_output=True);assert r.returncode!=0 and 'anchor' in (r.stdout+r.stderr);controls.append(n+' rejected')
assert blobs==24 and trees==8 and snap()==before
out={'status':'MATCH','payloads':len(names),'payload_bytes':sum(e['bytes'] for e in m['files']),'whole_files':len(before),'directories':len(dirs),'source_blobs':blobs,'source_trees':trees,'primary_pdf_bindings':len(primary),'original_copy_pairs':len(copies),'author_bytes_and_modes_unchanged':True,'controls':controls,'bundled_verifier':run.stdout.strip(),'mathematical_grade':False,'journal_scope_breach_not_repaired_by_artifact_checks':True}
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
