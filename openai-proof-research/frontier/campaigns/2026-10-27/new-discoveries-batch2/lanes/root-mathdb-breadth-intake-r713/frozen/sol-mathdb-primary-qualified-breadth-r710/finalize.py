from pathlib import Path
import json,hashlib,subprocess,datetime
P=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
excluded=['manifest.json','final-verification-receipt.json']
files=[{'path':str(p.relative_to(P)),'size':p.stat().st_size,'sha256':h(p)} for p in sorted(P.rglob('*')) if p.is_file() and str(p.relative_to(P)) not in excluded]
(P/'manifest.json').write_text(json.dumps({'excluded_exact_paths':excluded,'files':files},indent=2)+'\n')
tests=[]
for arg in [[],['--negative-hash'],['--negative-size'],['--negative-extra']]:
 r=subprocess.run(['python3','-B',str(P/'verify.py'),*arg],capture_output=True,text=True)
 assert r.returncode==(0 if not arg else 1),(arg,r.stdout,r.stderr)
 tests.append({'mode':arg or ['normal'],'exit':r.returncode,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','manifest_sha256':h(P/'manifest.json'),'manifest_size':(P/'manifest.json').stat().st_size,'tests':tests,'scientific_acceptance':False,'proposals':0,'literal_records':50,'complete':9,'definition_dependent':29,'scope_ambiguous':4,'incomplete':8,'baseline':8633,'scope':'exact originals,20chunks,8frozeninputs,three disjoint reservations,exact payload and literal/canonical identities','note':'Integrity is not mathematics or novelty PASS; current registry and successor bodies HOLD'}
(P/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
r=subprocess.run(['python3','-B',str(P/'verify.py')],capture_output=True,text=True);assert r.returncode==0,r.stderr
print(json.dumps(receipt,indent=2));print(r.stdout)
