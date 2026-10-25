#!/usr/bin/env python3
"""Authenticate this correctness review read-only; not a new mathematical review."""
from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[5];D=Path(__file__).resolve().parent;B=D.parent.parent
R=B/'arithmetic-r162bm-proof-r1';AR=B/'fresh-arithmetic-discovery-r162bm'
A={'FINAL.md':'477230d5e755df6dc3d44a079819dfa1671925033499aa2365772cd1b023a099','MANIFEST.json':'8ecbfecab4729a24f878ac6d178d53a7fbcb6670960ea52215de92a1a454c706','REPORT.md':'d5678ea28e03a3b2bf4246454b522f85b973c8845e308c2338270b0f24e183f9'}
def sha(a):return hashlib.sha256(a).hexdigest()
def pairs(xs):
 d={}
 for k,v in xs:assert k not in d;d[k]=v
 return d
def read(p):return json.loads(p.read_bytes(),object_pairs_hook=pairs)
def snap(root):
 d={}
 for p in root.rglob('*'):
  s=p.lstat();assert not stat.S_ISLNK(s.st_mode)
  if stat.S_ISREG(s.st_mode):
   a=p.read_bytes();d[p.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=s.st_mode)
  else:assert stat.S_ISDIR(s.st_mode)
 return d
before=read(D/'review-before.json');abefore=read(D/'author-before.json');assert snap(R)==before and snap(AR)==abefore
for n,h in A.items():assert sha((R/n).read_bytes())==h
run=subprocess.run(['python','-I','-B',str(R/'verify.py'),'--root',str(R),'--final-sha',A['FINAL.md'],'--manifest-sha',A['MANIFEST.json'],'--report-sha',A['REPORT.md']],cwd=P,capture_output=True,text=True)
assert run.returncode==0,(run.stdout,run.stderr)
m=read(R/'MANIFEST.json');names=[x['path'] for x in m['files']];assert names==sorted(set(names)) and len({x.casefold() for x in names})==len(names)
assert set(before)==set(names)|{'MANIFEST.json','REPORT.md'}
for x in m['files']:
 q=PurePosixPath(x['path']);assert not q.is_absolute() and '..' not in q.parts and str(q)==x['path']
 p=R/x['path'];s=p.lstat();a=p.read_bytes();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1 and len(a)==x['bytes'] and sha(a)==x['sha256'] and s.st_mode==x['st_mode']
dns=[x['path'] for x in m['directories']];assert dns==sorted(set(dns)) and set(dns)=={'.'}|{p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_dir()}
for x in m['directories']:assert (R/x['path']).stat().st_mode==x['st_mode']
for n,mode in m['control_modes'].items():assert (R/n).stat().st_mode==mode
raw=(P/'sources/preprints-tree.json').read_bytes();assert len(raw)==4858136 and sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(raw);prefix='preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026'
sel=read(R/'private/source-tree.json');expected=[x for x in tree['tree'] if x['path']==prefix or x['path'].startswith(prefix+'/')]
assert len(sel)==len(expected)==16 and {x['path']:x for x in sel}=={x['path']:x for x in expected}
blobs={x['path'][len(prefix)+1:]:x for x in sel if x['type']=='blob'};auth=read(R/'private/source-authentication.json');assert len(auth)==12 and {x['path'] for x in auth}==set(blobs)
for x in auth:
 p=R/'private/source'/x['path'];a=p.read_bytes();e=blobs[x['path']]
 assert len(a)==x['bytes']==e['size'] and sha(a)==x['sha256'] and hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==x['git_blob']==e['sha']
bi=read(R/'private/author-integrity-before.json');ai=read(R/'private/author-integrity-after.json');assert bi==ai and len(ai)==69
assert {x['path'] for x in ai}=={(AR/n).relative_to(P).as_posix() for n in abefore}
for x in ai:
 p=P/x['path'];a=p.read_bytes();assert len(a)==x['bytes'] and sha(a)==x['sha256'] and p.stat().st_mode==x['mode']
for x in read(R/'private/author-directory-integrity.json'):assert (P/x['path']).stat().st_mode==x['mode']
prim=read(R/'private/primary-input-authentication.json')
for x in prim:
 p=P/x['path'];assert p.is_relative_to(AR);a=p.read_bytes();assert len(a)==x['bytes'] and sha(a)==x['sha256'] and p.stat().st_mode==x['mode']
ns={'__name__':'artifact_intake','__file__':str(R/'verify.py')};exec(compile((R/'verify.py').read_bytes(),str(R/'verify.py'),'exec'),ns)
controls=[]
for i,n in enumerate(A):
 v=list(A.values());v[i]='0'*64
 try:ns['check'](R,*v)
 except AssertionError as ex:assert 'anchor mismatch' in str(ex);controls.append(n+' wrong anchor rejected')
 else:raise AssertionError('wrong anchor accepted')
fixture=R/'private/controls';tiny=ns['check'](fixture,*[sha((fixture/n).read_bytes()) for n in A])
assert snap(R)==before and snap(AR)==abefore
out=dict(status='MATCH',mathematical_gate_assigned_by_verifier=False,bundled_verifier=run.stdout.strip(),payloads=len(names),payload_bytes=sum(x['bytes'] for x in m['files']),whole_files=len(before),directories=len(dns),anchors=A,source_blobs=12,source_entries=16,author_originals=69,all_author_bytes_and_full_modes_unchanged=True,all_review_bytes_and_full_modes_unchanged=True,controls=controls,restored_tiny_fixture=tiny,statement_sha256=sha((AR/'STATEMENT.md').read_bytes()),proof_sha256=sha((AR/'private/PROOF.md').read_bytes()))
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
