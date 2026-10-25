#!/usr/bin/env python3
"""Read-only proof-review authentication; independent of mathematical verdict."""
from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[5];D=Path(__file__).resolve().parent;B=D.parent.parent
R=B/'arithmetic-r162bo-proof-r1';AR=B/'fresh-arithmetic-discovery-r162bo'
A={'FINAL.md':dict(sha256='2c493c2511d4887b13ea3eac2703402bbb949c2f116282c81e60b019cd247700',bytes=3418,mode=33188),'MANIFEST.json':dict(sha256='06afbe9b6a3ccd7f126174f8b1604938ea57c9caf6bc92054a0cb064b5679532',bytes=3718,mode=33188),'REPORT.md':dict(sha256='d3ac1f073284fc1f7eb854b472b64168cc14d70bbe8bf9c35735531346c10267',bytes=2752,mode=33188)}
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
for n,x in A.items():assert before[n]==x
args=[]
for n,flag in [('FINAL.md','--final'),('MANIFEST.json','--manifest'),('REPORT.md','--report')]:
 e=A[n];args.extend([flag,f"{e['sha256']}:{e['bytes']}:{e['mode']}"])
vp=R/'private/verify_packet.py';run=subprocess.run(['python','-I','-B',str(vp),str(R),*args],cwd=P,capture_output=True,text=True);assert run.returncode==0,(run.stdout,run.stderr)
m=read(R/'MANIFEST.json');names=[e['path'] for e in m['files']];assert names==sorted(set(names)) and len({n.casefold() for n in names})==len(names)
assert set(before)==set(names)|{'MANIFEST.json','REPORT.md'}
for e in m['files']:
 q=PurePosixPath(e['path']);assert not q.is_absolute() and '..' not in q.parts and str(q)==e['path'];p=R/e['path'];s=p.lstat();a=p.read_bytes()
 assert stat.S_ISREG(s.st_mode) and s.st_nlink==1 and len(a)==e['bytes'] and sha(a)==e['sha256'] and s.st_mode==e['mode']
dns=[e['path'] for e in m['directories']];assert dns==sorted(set(dns)) and set(dns)=={'.'}|{p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_dir()}
for e in m['directories']:assert (R/e['path']).stat().st_mode==e['mode']
first=read(R/'private/author-integrity-before.json');last=read(R/'private/author-integrity-after.json');assert len(first)==len(last)==60 and {e['path']:e for e in first}=={e['path']:e for e in last}
assert {e['path'] for e in first}=={(AR/n).relative_to(P).as_posix() for n in abefore}
for e in first:
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
for e in read(R/'private/author-directory-modes.json'):assert (P/e['path']).stat().st_mode==e['mode']
raw=(P/'sources/preprints-tree.json').read_bytes();assert len(raw)==4858136 and sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(raw);ca=read(R/'private/canonical-authentication.json');f='preprints/The-entropy-rate-dimension-formula-for-self-similar-measures-on-the-line-September-24-2026';expected=[e for e in tree['tree'] if e['path']==f or e['path'].startswith(f+'/')]
assert len(expected)==len(ca['selected'])==13 and {e['path']:e for e in expected}=={e['path']:e for e in ca['selected']}
ns={'__name__':'artifact','__file__':str(vp)};exec(compile(vp.read_bytes(),str(vp),'exec'),ns);controls=[]
for n in A:
 bad={k:dict(v) for k,v in A.items()};bad[n]['sha256']='0'*64
 try:ns['verify'](R,bad)
 except AssertionError as ex:assert 'anchor mismatch' in str(ex);controls.append(n+' wrong anchor rejected')
 else:raise AssertionError('wrong anchor accepted')
tiny=ns['verify'](R/'private/controls',read(R/'private/control-results.json')['anchors'])
assert snap(R)==before and snap(AR)==abefore
out=dict(status='MATCH',mathematical_grade=False,bundled_verifier=run.stdout.strip(),payloads=len(names),payload_bytes=sum(e['bytes'] for e in m['files']),whole_files=len(before),directories=len(dns),anchors=A,author_files_unchanged=60,review_bytes_and_modes_unchanged=True,author_bytes_and_modes_unchanged=True,controls=controls,restored_tiny_fixture=tiny,statement_sha256=sha((AR/'STATEMENT.md').read_bytes()),proof_sha256=sha((AR/'PROOF.md').read_bytes()))
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
