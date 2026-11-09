from pathlib import Path
import zipfile,subprocess,json,hashlib,datetime,sys
D=Path(__file__).resolve().parents[1];F=D/'fresh-replay';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
with zipfile.ZipFile(D/'331705-proof-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted((D/'formal').glob('*.lean')):z.write(p,p.name)
for p in F.iterdir():
 if p.is_file():p.unlink()
with zipfile.ZipFile(D/'331705-proof-source.zip') as z:z.extractall(F)
commands=[('build',['python',str(D/'scripts/replay_lean.py'),'-o','Cassinian.olean','Cassinian.lean']),('checker',['python',str(D/'scripts/checker.py')]),('audit',['python',str(D/'scripts/replay_lean.py'),'Audit.lean'])]
checks={}
for name,cmd in commands:
 log=D/f'outputs/fresh-{name}.log'
 with log.open('w') as f:p=subprocess.run(['python',str(D/'scripts/limited.py'),*cmd],stdout=f,stderr=subprocess.STDOUT,timeout=140)
 checks[name]={'returncode':p.returncode,'log_sha256':sha(log),'log':str(log.relative_to(D))};assert p.returncode==0,(name,log.read_text()[-2000:])
text=(D/'outputs/fresh-audit.log').read_text();rows=[s for s in text.splitlines() if 'INVENTORY|' in s];assert rows and all('|false|' in s and '|axiom|' not in s for s in rows)
for p in (D/'formal').glob('*.lean'):
 assert not __import__('re').search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',p.read_text()) if p.name!='Audit.lean' else True
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS_strict_fresh_extracted_rebuild_leanchecker_full_local_audit','checks':checks,'local_declarations':len(rows),'axioms':['propext','Classical.choice','Quot.sound'],'proof_packet_sha256':sha(D/'331705-proof-source.zip'),'Lean':'4.34.1','mathlib':'d13f23b723b8a846827a245b89c10fc7d3f11612','trust_limit':'Cached upstream oleans trusted, no full source-to-olean upstream rebuild claimed; 6GiB RSS sampled at100ms, not hard instantaneous cgroup RSS guarantee.','credit':0,'accepted_count_unchanged':'12/20 beyond39'}
(D/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
