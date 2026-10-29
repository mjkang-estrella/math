from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent
S=P.parent/'sol-fresh-source-discovery-r119'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
manifest=json.loads((S/'finalmanifest.json').read_text())['entries']
sources=json.loads((S/'source-lock.json').read_text())
for k,v in manifest.items():assert sha(S/k)==v,k
for k,v in sources.items():assert sha(S/k)==v,k
shutil.copy2(S/'checks.py',P/'copied-checks.py')
r=subprocess.run([sys.executable,str(P/'copied-checks.py')],capture_output=True,text=True,check=True)
(P/'checks.log').write_text(r.stdout+r.stderr)
j=json.loads((P/'check-results.json').read_text())
assert j['public_witness']['coefficient_periods']==[13,2,2,2,1,1,1]
assert j['relaxed_chains']['cases']==458 and not j['relaxed_chains']['failures']
for k,v in manifest.items():assert sha(S/k)==v,k
out={'status':'PASS','manifest_entries':len(manifest),'scientific_source_hashes':len(sources),'copied_checker_sha256':sha(P/'copied-checks.py'),'chain_diagnostics':458,'public_witness_periods':[13,2,2,2,1,1,1],'credit':0,'counts':[9,39],'qualification':'Classical quasipolynomial degree/period theorem is an explicit input. Finite chain tests are not a proof. Copied worker checker replay, not an independent implementation.'}
(P/'ADOPTION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
