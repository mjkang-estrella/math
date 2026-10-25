from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent;R=B/'arithmetic-r162cp-proof-r1';A=B/'fresh-arithmetic-discovery-r162cp'
def sha(a):return hashlib.sha256(a).hexdigest()
def unique(pairs):
 d={}
 for k,v in pairs:assert k not in d;d[k]=v
 return d
def read(p):return json.loads(p.read_bytes(),object_pairs_hook=unique)
def snap(root):
 out={}
 for p in root.rglob('*'):
  m=p.lstat().st_mode;assert not stat.S_ISLNK(m)
  if stat.S_ISREG(m):
   a=p.read_bytes();out[p.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=m)
  else:assert stat.S_ISDIR(m)
 return out
before=read(D/'private/proof-intake/root-before.json');author=read(D/'private/proof-intake/author-before.json');assert snap(R)==before and snap(A)==author
anchors={'FINAL.md':'c611c086fc283f396300742ec632544666b3f9ebe5157dca4591738df361e1b2','MANIFEST.json':'4a28dc259e7cd932f37d612701d7d50709cdbf2a1d533b1b6d2fb305ebe522c5','REPORT.md':'34d53f9038838308c24aa6e63a8f697f3f65db54b3c813e1ddb3011f3e10ad45'}
for n,h in anchors.items():assert before[n]['sha256']==h and before[n]['mode']==33188
args=['--root',str(R)]
for k,h in zip(['final-sha256','manifest-sha256','report-sha256'],anchors.values()):args+=['--'+k,h]
v=R/'verify_packet.py';r=subprocess.run(['python3','-I','-B',str(v),*args],cwd=P,text=True,capture_output=True);assert r.returncode==0,(r.stdout,r.stderr)
m=read(R/'MANIFEST.json');names=[e['path'] for e in m['files']];assert len(names)==19 and names==sorted(set(names)) and len({n.casefold() for n in names})==19 and set(before)==set(names)|set(anchors)-{'FINAL.md'}
for e in m['files']:
 n=e['path'];p=PurePosixPath(n);assert not p.is_absolute() and '..' not in p.parts and str(p)==n and '\\' not in n
 assert before[n]=={k:e[k] for k in ['bytes','sha256','mode']}
side=read(D/'private/review-inputs.json');assert len(side['files'])==68
for e in side['files']:
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.lstat().st_mode==e['mode']
controls=[]
for i,n in enumerate(anchors):
 bad=args.copy();bad[3+2*i]='0'*64;t=subprocess.run(['python3','-I','-B',str(v),*bad],cwd=P,text=True,capture_output=True);assert t.returncode!=0 and 'anchor mismatch' in t.stderr;controls.append(n+' rejected')
assert snap(R)==before and snap(A)==author
out=dict(status='MATCH',mathematical_gate=False,bundled_verifier=r.stdout.strip(),payloads=19,whole_files=len(before),payload_bytes=sum(e['bytes'] for e in m['files']),anchors=anchors,author_inputs_checked=68,author_bytes_modes_unchanged=True,review_bytes_modes_unchanged=True,controls=controls,limit='Review manifest binds file modes;directory modes not included in its manifest. Exact file membership and before/after bytes/full file modes independently checked.')
(D/'proof-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
