from pathlib import Path
import json,hashlib,subprocess,sys,datetime
P=Path(__file__).resolve().parent
G=P.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
def entry(p):
 b=p.read_bytes();return {'path':str(p.relative_to(P)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
ex=['manifest.json','final-verification-receipt.json']
m={'excluded_exact_paths':ex,'files':[entry(p) for p in sorted(P.rglob('*')) if p.is_file() and str(p.relative_to(P)) not in ex]}
(P/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
results={}
for flag in ['--negative-hash','--negative-size','--negative-extra','']:
 args=[sys.executable,'-B',str(G),sys.executable,'-B',str(P/'verify.py')]+([flag] if flag else [])
 r=subprocess.run(args,capture_output=True,text=True);results[flag or 'positive']={'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
 assert (r.returncode!=0 if flag else r.returncode==0),results
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':entry(P/'manifest.json'),'integrity':'PASS','tests':results,'baseline_literal_reviews':8533,'new_literal_reviews':50,'complete_statements':8,'definition_dependent':21,'scope_ambiguous':11,'incomplete':10,'proposals':0,'credit':0,'original_chunks':20,'frozen_inputs':8,'math_acceptance':False,'registry_and_novelty':'HOLD','counts':{'additional':9,'total':39,'next':40}}
(P/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'manifest':receipt['manifest'],'tests':{k:v['exit'] for k,v in results.items()}}))
