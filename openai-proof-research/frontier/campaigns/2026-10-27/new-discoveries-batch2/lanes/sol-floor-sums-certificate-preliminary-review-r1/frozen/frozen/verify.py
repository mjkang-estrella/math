import pathlib,json,hashlib,datetime,sys,itertools
L=pathlib.Path(__file__).parent
def h(p):
 s=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):s.update(b)
 return s.hexdigest()
manifest=json.loads((L/'manifest.json').read_text())
assert 'manifest.json' not in manifest and 'verification-receipt.json' not in manifest
assert set(manifest)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
for name,sha in manifest.items():assert h(L/name)==sha,name
bindings=json.loads((L/'scientificbindings.json').read_text())
for b in bindings:assert h(pathlib.Path(b['original']))==h(pathlib.Path(b['copy']))==b['sha256'],b
ledger=json.loads((L/'administrative-ledger.json').read_text())
assert (ledger['accepted_count'],ledger['total_accepted_count'],ledger['next_global_outcome_number'])==(9,39,40)
sys.path.insert(0,str(L/'tools'));import z3
solver=z3.Solver();solver.set(timeout=180000);solver.from_string((L/'all-m-query.smt2').read_text());result=solver.check();assert result==z3.unsat
# Separate implementation checks the quotient-free clipping bridge itself,
# including empty subsets and H=m, without inferring an all-m result.
checks=0
for m in range(1,10):
 for H in range(1,m+1):
  for s in range(0,4*(m-1)+1):
   direct=sum((j+s)//m for j in range(H))
   clips=sum(max(0,min(H,s+H-q*m)) for q in range(1,5))
   assert direct==clips
   checks+=1
# Mathematical input files still equal their manifested content after replay.
for name,sha in manifest.items():assert h(L/name)==sha,name
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS file integrity, source bindings and computational replay ONLY','manifest_sha256':h(L/'manifest.json'),'manifest_files':len(manifest),'source_bindings':len(bindings),'manifest_excludes_itself_and_receipt':True,'solver_replay':str(result),'solver_version':z3.get_version_string(),'separate_clip_bridge_checks':checks,'ordinary_proof':False,'solver_proof_independently_checked':False,'accepted_count_change':0,'counts':[9,39,40]}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
