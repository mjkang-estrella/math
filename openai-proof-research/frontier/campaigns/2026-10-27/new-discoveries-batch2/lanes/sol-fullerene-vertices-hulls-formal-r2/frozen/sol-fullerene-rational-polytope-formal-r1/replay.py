from pathlib import Path
import os,subprocess,sys,json,zipfile,hashlib,re
L=Path(__file__).resolve().parent
D=L/'replay'/'fresh'
D.mkdir(parents=True,exist_ok=False)
with zipfile.ZipFile(L/'geometry-source.zip') as z:z.extractall(D)
for s,h in json.loads((D/'archive-files.json').read_text()).items():assert hashlib.sha256((D/s).read_bytes()).hexdigest()==h
for module in ['Literal','InstanceG','InstanceH','Inventory','Audit']:
 args=[sys.executable,str(D/'runner.py')]
 if module not in ['Inventory','Audit']:args+=['-o',module+'.olean']
 r=subprocess.run(args+[module+'.lean'],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (D/(module+'-replay.log')).write_text(r.stdout)
 assert r.returncode==0,(module,r.returncode,r.stdout[-2000:])
 logs=list(D.glob('attempt-*.log'))
 assert not any('PANIC' in p.read_text() or 'error:' in p.read_text() or 'sorryAx' in p.read_text() for p in logs)
audit='\n'.join(p.read_text() for p in D.glob('attempt-*.log'))
allowed={'propext','Classical.choice','Quot.sound'}
for group in re.findall(r'depends on axioms: \[([^\]]*)\]',audit,re.S):
 assert {x.strip() for x in group.split(',') if x.strip()}<=allowed,group
owned=re.findall(r'OWN_DECL (\S+)',audit)
assert owned and 'TRANSITIVE_SAFE_COUNT' in audit
(L/'owned-declarations.json').write_text(json.dumps(owned,indent=2)+'\n')
for p in D.rglob('*'):
 if p.suffix in ['.olean','.ilean','.c','.o','.ir'] or '.olean.' in p.name:p.unlink()
(L/'replay-receipt.json').write_text(json.dumps(dict(status='PASS',scope='Staged geometry only; no complete vertex/facet or SourceClaim endpoint',owned_declarations=len(owned),allowed_axioms=sorted(allowed),source_only=True,serial=True,archive_sha256=hashlib.sha256((L/'geometry-source.zip').read_bytes()).hexdigest()),indent=2)+'\n')
print('Fresh extracted replay and declaration audit PASS:',len(owned),'owned declarations')
