#!/usr/bin/env python3
"""Read-only contribution-artifact checks, separate from mathematical grading."""
from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[5];D=Path(__file__).resolve().parent;B=D.parent.parent
R=B/'arithmetic-r162bm-contribution-r1';AR=B/'fresh-arithmetic-discovery-r162bm'
A={'FINAL.md':'700f2be828c96125bd0ad833c2a5f00242c73e29bc93c2bd50c16bd27573a926','MANIFEST.json':'50f47982776d04f4b8b7b9f68876faa380c5e9500810ef5ec00272ba53d0dda1','REPORT.md':'3a0c02e5276da6bf8c589cebdb928a4fc374867abfad902aee17f7f053c022b3'}
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
for n,h in A.items():assert sha((R/n).read_bytes())==h
run=subprocess.run(['python','-I','-B',str(R/'verify.py'),'--root',str(R),'--final-sha',A['FINAL.md'],'--manifest-sha',A['MANIFEST.json'],'--report-sha',A['REPORT.md']],cwd=P,capture_output=True,text=True)
assert run.returncode==0,(run.stdout,run.stderr)
m=read(R/'MANIFEST.json');names=[e['path'] for e in m['files']];assert names==sorted(set(names)) and len(set(n.casefold() for n in names))==len(names)
assert set(before)==set(names)|{'MANIFEST.json','REPORT.md'}
for e in m['files']:
 n=e['path'];q=PurePosixPath(n);assert not q.is_absolute() and '..' not in q.parts and str(q)==n
 p=R/n;a=p.read_bytes();s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1 and len(a)==e['bytes'] and sha(a)==e['sha256'] and s.st_mode==e['mode']
dns=[e['path'] for e in m['directories']];assert dns==sorted(set(dns)) and set(dns)=={'.'}|{p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_dir()}
for e in m['directories']+m['outside_manifest']:assert (R/e['path']).stat().st_mode==e['mode']
initial=read(R/'private/author-integrity-initial.json');final=read(R/'private/author-integrity-final.json');assert final['unchanged'] and len(initial)==len(final['files'])==69
assert {e['path'] for e in final['files']}=={(AR/n).relative_to(P).as_posix() for n in abefore}
for e in initial:
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes']==e['actual_bytes'] and sha(a)==e['sha256']==e['actual_sha256'] and p.stat().st_mode==e['mode']==e['actual_mode']
for e in final['files']:
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
for e in final['directories']:assert (P/e['path']).stat().st_mode==e['mode']
raw=(P/'sources/preprints-tree.json').read_bytes();assert len(raw)==4858136 and sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(raw);sa=read(R/'private/source-authentication.json');prefix='preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026'
sel=[e for e in tree['tree'] if e['path']==prefix or e['path'].startswith(prefix+'/')]
assert len(sa['selected'])==len(sel)==16 and {e['path']:e for e in sa['selected']}=={e['path']:e for e in sel}
blobs={e['path']:e for e in sel if e['type']=='blob'};assert len(sa['blobs'])==len(blobs)==12
for e in sa['blobs']:
 a=(AR/'private/source'/e['path'][len(prefix)+1:]).read_bytes();b=blobs[e['path']]
 assert len(a)==e['bytes']==b['size'] and sha(a)==e['sha256'] and hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==e['git_blob']==b['sha']
ns={'__name__':'readonly','__file__':str(R/'verify.py')};exec(compile((R/'verify.py').read_bytes(),str(R/'verify.py'),'exec'),ns)
controls=[]
for i,n in enumerate(A):
 a=list(A.values());a[i]='0'*64
 try:ns['verify'](R,*a)
 except ValueError as ex:assert 'anchor mismatch' in str(ex);controls.append(n+' wrong anchor rejected')
 else:raise AssertionError('wrong anchor accepted')
tiny=R/'private/control-fixture';restored=ns['verify'](tiny,*[sha((tiny/n).read_bytes()) for n in A])
assert snap(R)==before and snap(AR)==abefore
out=dict(status='MATCH',mathematical_gate_assigned_by_verifier=False,bundled_verifier=run.stdout.strip(),payloads=len(names),payload_bytes=sum(e['bytes'] for e in m['files']),whole_files=len(before),directories=len(dns),anchors=A,source_entries=16,source_blobs=12,author_files_unchanged=69,review_bytes_and_modes_unchanged=True,author_bytes_and_modes_unchanged=True,controls=controls,restored_fixture=restored)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
