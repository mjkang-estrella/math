#!/usr/bin/env python3
"""Read-only r162bn artifact checks; no mathematical grade."""
from pathlib import Path,PurePosixPath
import hashlib,json,stat,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;R=D.parent/'fresh-arithmetic-discovery-r162bn'
A={'FINAL.md':'d1b6fa9a3e0831b2c5e97f29dff228204f0294016aeb32e78bd15255662e8002','MANIFEST.json':'37d5919637b6feba770b7cbea4a5534049ab635cf499898ca89c8a178b2a4f34','REPORT.md':'eae18ada47c5adfe69cc2122538c53912469eb5458bd77c97148e0cd059afe70'}
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
for n,h in A.items():assert sha((R/n).read_bytes())==h
run=subprocess.run(['python','-I','-B',str(R/'verify.py'),'--root',str(R),'--manifest-sha256',A['MANIFEST.json'],'--final-sha256',A['FINAL.md'],'--report-sha256',A['REPORT.md'],'--project',str(P)],cwd=P,capture_output=True,text=True)
assert run.returncode==0,(run.stdout,run.stderr)
m=read(R/'MANIFEST.json');names=[e['path'] for e in m['files']];assert names==sorted(set(names)) and len({n.casefold() for n in names})==len(names)
assert set(before)==set(names)|{'MANIFEST.json','REPORT.md'}
for e in m['files']:
 q=PurePosixPath(e['path']);assert not q.is_absolute() and '..' not in q.parts and str(q)==e['path']
 p=R/e['path'];a=p.read_bytes();s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1 and len(a)==e['bytes'] and sha(a)==e['sha256'] and s.st_mode==e['mode']
dns=[e['path'] for e in m['directories']];assert dns==sorted(set(dns)) and set(dns)=={'.'}|{p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_dir()}
for e in m['directories']:assert (R/e['path']).stat().st_mode==e['mode']
sel=read(R/'private/source-bindings.json');raw=(P/'sources/preprints-tree.json').read_bytes();assert len(raw)==4858136 and sha(raw)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(raw);assert not tree['truncated'] and len(tree['tree'])==13223
folders=[e['path'] for e in sel if e['type']=='tree' and e['path'].count('/')==1];assert len(folders)==2
expected=[e for e in tree['tree'] if any(e['path']==f or e['path'].startswith(f+'/') for f in folders)]
assert len(sel)==len(expected)==39 and {e['path']:e for e in sel}=={e['path']:e for e in expected}
ledger=read(D/'private/completed-direct-inputs.json');copies=read(R/'private/completed-bindings.json');assert len(ledger)==len(copies)==5
for e,c in zip(ledger,copies):
 assert e['path']==c['original'] and e['bytes']==c['bytes'] and e['sha256']==c['sha256'] and e['mode']==c['mode']
 p=P/e['path'];a=p.read_bytes();assert p.stat().st_mode==e['mode'] and sha(a)==e['sha256'] and len(a)==e['bytes'] and a==(R/c['copy']).read_bytes()
ns={'__name__':'artifact','__file__':str(R/'verify.py')};exec(compile((R/'verify.py').read_bytes(),str(R/'verify.py'),'exec'),ns)
controls=[]
for n in A:
 b=dict(A);b[n]='0'*64
 try:ns['verify'](R,b['MANIFEST.json'],b['FINAL.md'],b['REPORT.md'],P)
 except AssertionError as ex:assert 'anchor' in str(ex);controls.append(n+' wrong anchor rejected')
 else:raise AssertionError('wrong anchor accepted')
tiny=R/'private/tiny-control';th={n:sha((tiny/n).read_bytes()) for n in A};restored=ns['verify'](tiny,th['MANIFEST.json'],th['FINAL.md'],th['REPORT.md'],P)
assert snap(R)==before
out=dict(status='MATCH',mathematical_grade=False,bundled_verifier=run.stdout.strip(),payload_files=len(names),payload_bytes=sum(e['bytes'] for e in m['files']),whole_files=len(before),directories=len(dns),source_entries=39,source_blobs=30,canonical_text_objects=28,canonical_text_bytes=601146,original_copy_pairs=5,all_bytes_and_full_modes_unchanged=True,anchors=A,controls=controls,restored_tiny_fixture=restored)
(D/'verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
