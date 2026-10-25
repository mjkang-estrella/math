from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent;R=B/'arithmetic-r162cp-contribution-r1';A=B/'fresh-arithmetic-discovery-r162cp'
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
before=read(D/'private/contribution-intake/root-before.json');author=read(D/'private/contribution-intake/author-before.json');assert snap(R)==before and snap(A)==author
anchors={'FINAL.md':'753e2e7c2fc55e522840b6b4997c1338bf49f15eeb8065c5388b598654ecbdb3','MANIFEST.json':'8c3f103a14bb9a7fb7eb419fcbeec04c98b0437d43d7d4e896d421de3c9b1117','REPORT.md':'514575c9536b529d73ddb092918130882631241ec3a670afd4d3919eaf7ba350'}
for n,h in anchors.items():assert before[n]['sha256']==h and before[n]['mode']==33188
args=['--root',str(R)]
for k,h in zip(['final-sha256','manifest-sha256','report-sha256'],anchors.values()):args+=['--'+k,h]
v=R/'verify_packet.py';r=subprocess.run(['python3','-I','-B',str(v),*args],cwd=P,text=True,capture_output=True);assert r.returncode==0,(r.stdout,r.stderr)
m=read(R/'MANIFEST.json');names=[e['path'] for e in m['files']];assert len(names)==38 and names==sorted(set(names)) and len({n.casefold() for n in names})==38 and set(before)==set(names)|set(anchors)-{'FINAL.md'}
for e in m['files']:
 n=e['path'];p=PurePosixPath(n);assert not p.is_absolute() and '..' not in p.parts and str(p)==n and '\\' not in n
 assert before[n]=={k:e[k] for k in ['bytes','sha256','mode']}
side=read(D/'private/review-inputs.json');assert len(side['files'])==68
for e in side['files']:
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.lstat().st_mode==e['mode']
dirs={'.':R.stat().st_mode};dirs.update({p.relative_to(R).as_posix():p.stat().st_mode for p in R.rglob('*') if p.is_dir()});assert dirs=={x['path']:x['mode'] for x in m['directories']}
primary=read(R/'private/primary/public-authentication.json')+[dict(name='DDv3',**read(R/'private/primary/DDv3-binding.json'))]
assert len(primary)==6
for e in primary:
 a=(R/'private/primary'/(e['name']+'.pdf')).read_bytes();assert a.startswith(b'%PDF') and len(a)==e['bytes'] and sha(a)==e['sha256']
controls=[]
for i,n in enumerate(anchors):
 bad=args.copy();bad[3+2*i]='0'*64;t=subprocess.run(['python3','-I','-B',str(v),*bad],cwd=P,text=True,capture_output=True);assert t.returncode!=0 and 'anchor mismatch' in t.stderr;controls.append(n+' rejected')
assert snap(R)==before and snap(A)==author
out=dict(status='MATCH',mathematical_gate=False,bundled_verifier=r.stdout.strip(),payloads=38,whole_files=len(before),payload_bytes=sum(e['bytes'] for e in m['files']),anchors=anchors,author_inputs_checked=68,author_bytes_modes_unchanged=True,review_bytes_modes_unchanged=True,controls=controls,directories=len(dirs),primary_pdf_bindings=len(primary),limit='Exact membership, file/directory full modes and original author bytes checked;artifact only.')
(D/'contribution-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
