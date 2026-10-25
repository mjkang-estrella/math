#!/usr/bin/env python3
"""Read-only artifact checks; no mathematical verdict generated here."""
from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[5];D=Path(__file__).resolve().parent;B=D.parent.parent
R=B/'arithmetic-r162bo-contribution-r1';AR=B/'fresh-arithmetic-discovery-r162bo'
A={'FINAL.md':dict(sha256='4c8cc368c7dbd8e0fd1049151322b8eb3be3c0aae1063dede026bafb9c29308d',bytes=2822,mode=33188),'MANIFEST.json':dict(sha256='69f606fc37591b0fce60cf6ef553c670107818e2d84e390a60ed138402812762',bytes=5068,mode=33188),'REPORT.md':dict(sha256='c1c0b97755c87b2e97fd89cb49b76fad55be56be412e553c4e9ce47ed9f1b2a5',bytes=2939,mode=33188)}
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
before=read(D/'review-before.json');abefore=read(D/'author-before.json');assert snap(R)==before and snap(AR)==abefore
for n,e in A.items():assert before[n]==e
args=[]
for n,k in [('FINAL.md','final'),('MANIFEST.json','manifest'),('REPORT.md','report')]:args.extend(['--'+k+'-sha',A[n]['sha256'],'--'+k+'-bytes',str(A[n]['bytes'])])
vp=R/'private/verify.py';run=subprocess.run(['python','-I','-B',str(vp),'--root',str(R),*args],cwd=P,capture_output=True,text=True);assert run.returncode==0,(run.stdout,run.stderr)
m=read(R/'MANIFEST.json');names=[e['path'] for e in m['files']];assert names==sorted(set(names)) and len({n.casefold() for n in names})==len(names) and set(before)==set(names)|{'MANIFEST.json','REPORT.md'}
for e in m['files']:
 q=PurePosixPath(e['path']);assert not q.is_absolute() and '..' not in q.parts and str(q)==e['path'];p=R/e['path'];a=p.read_bytes();s=p.lstat()
 assert stat.S_ISREG(s.st_mode) and s.st_nlink==1 and len(a)==e['bytes'] and sha(a)==e['sha256'] and s.st_mode==e['mode']
dns=[e['path'] for e in m['directories']];assert dns==sorted(set(dns)) and set(dns)=={'.'}|{p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_dir()}
for e in m['directories']:assert (R/e['path']).stat().st_mode==e['mode']
ai=read(R/'private/author-integrity.json');assert len(ai)==60 and {e['path'] for e in ai}=={(AR/n).relative_to(P).as_posix() for n in abefore}
for e in ai:
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
raw=(P/'sources/preprints-tree.json').read_bytes();assert len(raw)==4858136 and sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(raw);by={e['path']:e for e in tree['tree']};ca=read(R/'private/canonical-authentication.json');assert len(ca['blobs'])==10
for e in ca['blobs']:
 p=AR/'private/source'/e['path'];a=p.read_bytes();b=by[e['path']];assert len(a)==e['bytes']==b['size'] and sha(a)==e['sha256'] and hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['git_sha1']==b['sha']
g=read(R/'private/gsv-acquisition.json')
for ext,key in [('pdf',''),('txt','extract_')]:
 a=(R/'private'/('gsv-2004.'+ext)).read_bytes();assert len(a)==g[key+'bytes'] and sha(a)==g[key+'sha256']
ns={'__name__':'artifact','__file__':str(vp)};exec(compile(vp.read_bytes(),str(vp),'exec'),ns);controls=[]
for n in A:
 bad={k:dict(v) for k,v in A.items()};bad[n]['sha256']='0'*64
 try:ns['verify'](R,bad)
 except ValueError as ex:assert 'anchor mismatch' in str(ex);controls.append(n+' wrong anchor rejected')
 else:raise AssertionError('wrong anchor accepted')
tiny=ns['verify'](R/'private/controls',read(R/'private/control-results.json')['anchors']);assert snap(R)==before and snap(AR)==abefore
out=dict(status='MATCH',mathematical_grade=False,bundled_verifier=run.stdout.strip(),payloads=len(names),payload_bytes=sum(e['bytes'] for e in m['files']),whole_files=len(before),directories=len(dns),anchors=A,author_files_unchanged=60,review_bytes_and_modes_unchanged=True,author_bytes_and_modes_unchanged=True,source_blobs=10,classical_primary_pdf_and_extract_matched=True,controls=controls,restored_tiny_fixture=tiny)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
