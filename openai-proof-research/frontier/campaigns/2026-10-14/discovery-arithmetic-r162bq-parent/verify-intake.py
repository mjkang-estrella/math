#!/usr/bin/env python3
"""Read-only artifact checks; no mathematical gate."""
from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;R=D.parent/'fresh-arithmetic-discovery-r162bq'
A={'FINAL.md':'b8245a0343d4eac09380349f74b379052301ac84bd502673ae61ee9541c325c6','private/MANIFEST.json':'1c4f3ebdb701ba6144c0d52a1ee9818c039f9854fe1afd6d355d391d5e809254','REPORT.md':'f1cfd10918bd40b08c0212fdde28e6b16461107bf8760449680091c461202224'}
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
vp=R/'private/verify.py';args=[]
for n,k in zip(A,['final','manifest','report']):args.extend(['--'+k+'-sha256',A[n]])
run=subprocess.run(['python','-I','-B',str(vp),*args],cwd=P,capture_output=True,text=True);assert run.returncode==0,(run.stdout,run.stderr)
m=read(R/'private/MANIFEST.json');names=[e['path'] for e in m['files']];assert names==sorted(set(names)) and len({n.casefold() for n in names})==len(names)
assert set(before)==set(names)|{'private/MANIFEST.json','REPORT.md'}
for e in m['files']:
 q=PurePosixPath(e['path']);assert not q.is_absolute() and '..' not in q.parts and str(q)==e['path'] and '\\' not in e['path'];p=R/e['path'];a=p.read_bytes();s=p.lstat()
 assert stat.S_ISREG(s.st_mode) and s.st_nlink==1 and len(a)==e['size'] and sha(a)==e['sha256'] and s.st_mode==e['mode']
dns=[e['path'] for e in m['directories']];assert dns==sorted(set(dns)) and set(dns)=={'.'}|{p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_dir()}
for e in m['directories']:assert (R/e['path']).stat().st_mode==e['mode']
raw=(P/'sources/preprints-tree.json').read_bytes();assert len(raw)==4858136 and sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=read(P/'sources/preprints-tree.json');assert tree['truncated'] is False;by={e['path']:e for e in tree['tree']};ca=read(R/'private/source-bindings.json');assert len(ca)==13
for e in ca:
 a=(R/e['local']).read_bytes();b=by[e['path']];assert len(a)==e['size']==b['size'] and sha(a)==e['sha256'] and hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['git_blob']==b['sha']
ns={'__name__':'artifact','__file__':str(vp)};exec(compile(vp.read_bytes(),str(vp),'exec'),ns);controls=[]
for i,n in enumerate(A):
 bad=list(A.values());bad[i]='0'*64
 try:ns['verify_packet'](R,(R/'private/MANIFEST.json').read_bytes(),(R/'REPORT.md').read_bytes(),bad)
 except ValueError as ex:assert str(ex)==('MANIFEST' if i==1 else n[:-3])+' detached anchor mismatch';controls.append(n+' wrong anchor rejected')
 else:raise AssertionError('wrong anchor accepted')
assert snap(R)==before
out=dict(status='MATCH',mathematical_grade=False,bundled_verifier=run.stdout.strip(),payloads=len(names),payload_bytes=sum(e['size'] for e in m['files']),whole_files=len(before),directories=len(dns),anchors=A,author_bytes_and_modes_unchanged=True,source_blobs=13,source_trees_verified_by_bundled_verifier=6,primary_pdf_and_extract_pairs=6,completed_originals_and_copies=5,controls=controls,recorded_author_controls=(R/'private/CONTROL-RESULTS.md').read_text())
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
