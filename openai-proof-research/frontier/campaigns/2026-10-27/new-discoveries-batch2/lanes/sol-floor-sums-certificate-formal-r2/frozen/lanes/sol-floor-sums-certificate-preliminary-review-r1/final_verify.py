from pathlib import Path
import json,hashlib,subprocess,sys,os,time
L=Path(__file__).resolve().parent;F=L/'frozen';start=time.monotonic()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
M=json.loads((L/'final-manifest.json').read_text())
def verify():
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in [] and str(p.relative_to(L)) not in ['final-manifest.json','final-verification-receipt.json']}
 assert actual==set(M['files'])
 for rel,h in M['files'].items():assert sha(L/rel)==h,rel
 for r in json.loads((L/'freeze.json').read_text()):assert sha(Path(r['original']))==sha(L/r['copy'])==r['sha256']
 for r in json.loads((F/'bindings.json').read_text())['files']:assert sha(Path(r['original']))==sha(F/r['copy'])==r['sha256']
verify()
admin={}
for name in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/name).read_text());admin[name]={'keys':list(d),'accepted_titles':[r.get('title') for r in d.get('accepted',[])], 'counts':{k:d.get(k) for k in ['accepted_count','total_accepted_count','next_global_outcome_number']}}
assert admin['ledger.json']['counts']=={'accepted_count':9,'total_accepted_count':39,'next_global_outcome_number':40}
env=dict(os.environ,CERT_VERIFY_ONLY='1',PATH='/solver-unavailable');runs=[]
for script in ['mapping.py','check.py']:
 p=subprocess.run([sys.executable,str(L/'deny_solver.py'),str(F/script)],capture_output=True,text=True,env=env)
 assert p.returncode==0,p.stderr
 d=json.loads(p.stdout)
 if script=='mapping.py':assert d==json.loads((F/'query-map.json').read_text())
 else:assert d['certificate_PASS'] and d['root_closed'] and d['root_conclusion']=='false' and d['used_proof_nodes']==12459 and d['gap_nodes']==0
 runs.append({'script':script,'exit':p.returncode,'stdout':d,'stderr':p.stderr})
verify()
receipt={'status':'PASS','manifest_sha256':sha(L/'final-manifest.json'),'originals_and_copies_unchanged':True,'administrative_snapshot_read':admin,'counts_unchanged':[9,39,40],'runs':runs,'seconds':time.monotonic()-start,'limits':{'AS_and_group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230},'not_Lean':True}
(L/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'status':'PASS','seconds':receipt['seconds'],'counts':[9,39,40]}))
