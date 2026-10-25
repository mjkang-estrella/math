#!/usr/bin/env python3
"""Independent read-only artifact checks; no mathematical gate."""
from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;R=D.parent/'fresh-arithmetic-discovery-r162bz'
A={'FINAL.md':'2c77405fc52fee37cb57316736a2a6bc23f60a7d42fc0166715f1b8e77af3de3','private/MANIFEST.json':'f3a44315a692109055cca9eae68e457a2be349e6c69e30bfdf50989022cdb4d7','REPORT.md':'60440ef92299b5880be1257ec77d1a668c2e35bde55e236432f2cdb105cfd7f7'}
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
before=read(D/'private/intake/root-before.json');assert snap(R)==before
for n,a in A.items():assert before[n]['sha256']==a and before[n]['mode']==33188
vp=R/'private/verify_packet.py';args=['--root',str(R)]
for n,k in zip(A,['final-sha','manifest-sha','report-sha']):args.extend(['--'+k,A[n]])
run=subprocess.run(['python','-I','-B',str(vp),*args],cwd=P,capture_output=True,text=True)
assert run.returncode==0,(run.stdout,run.stderr)
m=read(R/'private/MANIFEST.json');names=[e['path'] for e in m['files']]
assert names==sorted(set(names)) and len({n.casefold() for n in names})==len(names)
assert set(before)==set(names)|{'private/MANIFEST.json','REPORT.md'}
for e in m['files']:
 q=PurePosixPath(e['path']);assert not q.is_absolute() and '..' not in q.parts and str(q)==e['path'] and '\\' not in e['path']
 p=R/e['path'];a=p.read_bytes();s=p.lstat()
 assert stat.S_ISREG(s.st_mode) and s.st_nlink==1 and len(a)==e['bytes'] and sha(a)==e['sha256'] and s.st_mode==e['mode']
dirs={'.':R.stat().st_mode};dirs.update({p.relative_to(R).as_posix():p.stat().st_mode for p in R.rglob('*') if p.is_dir()})
assert dirs=={e['path']:e['mode'] for e in m['directories']}
raw=(P/'sources/preprints-tree.json').read_bytes();assert len(raw)==4858136 and sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=read(P/'sources/preprints-tree.json');assert tree['truncated'] is False
by={e['path']:e for e in tree['tree']};blobs=0;trees=0
for family in ['source','companion']:
 selected=read(R/('private/'+family+'-tree.json'))
 for e in selected:assert by[e['path']]==e
 for parent in [e for e in selected if e['type']=='tree']:
  children=[e for e in selected if str(PurePosixPath(e['path']).parent)==parent['path']]
  children.sort(key=lambda e:(PurePosixPath(e['path']).name+('/' if e['type']=='tree' else '')).encode())
  body=b''.join((e['mode'].lstrip('0')+' '+PurePosixPath(e['path']).name).encode()+b'\0'+bytes.fromhex(e['sha']) for e in children)
  assert hashlib.sha1(b'tree '+str(len(body)).encode()+b'\0'+body).hexdigest()==parent['sha'];trees+=1
 for e in read(R/('private/'+family+'-bindings.json')):
  a=(P/e['local']).read_bytes();meta=by[e.get('original',e.get('path'))]
  assert len(a)==e['bytes']==meta['size'] and sha(a)==e['sha256']
  assert hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['git_blob']==meta['sha'];blobs+=1
controls=[]
for i,n in enumerate(A):
 bad=args.copy();bad[3+2*i]='0'*64
 test=subprocess.run(['python','-I','-B',str(vp),*bad],cwd=P,capture_output=True,text=True)
 assert test.returncode!=0 and 'anchor mismatch: '+n in test.stderr;controls.append(n+' wrong anchor rejected')
assert snap(R)==before
out=dict(status='MATCH',mathematical_grade=False,bundled_verifier=run.stdout.strip(),payloads=len(names),payload_bytes=sum(e['bytes'] for e in m['files']),whole_files=len(before),directories=len(dirs),anchors=A,author_bytes_and_modes_unchanged=True,source_and_companion_blobs=blobs,source_trees_independently_verified=trees,primary_pdf_bindings=4,completed_originals_and_copies=5,controls=controls,recorded_author_controls=(R/'private/CONTROL-RESULTS.md').read_text())
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
