from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;B=P.parents[1]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
out={}
for n in [128,129]:
 S=P.parent/f'sol-fresh-source-discovery-r{n}'
 m=json.loads((S/('finalmanifest.json' if n==128 else 'manifest.json')).read_text())
 if n==128:m=m['entries']
 for r in m:assert sha(S/r['path'])==r['sha256'] and (S/r['path']).stat().st_size==r['bytes'],r['path']
 if n==128:
  shutil.copy2(S/'checks.py',P/'copied-checks.py')
  r=subprocess.run([sys.executable,str(P/'copied-checks.py')],capture_output=True,text=True,check=True)
  (P/'checks.log').write_text(r.stdout+r.stderr);j=json.loads(r.stdout)
  assert j['status']=='PASS' and len(j['cases'])==12
  lock=json.loads((S/'source-lock.json').read_text())
  for r in lock:assert sha(S/r['path'])==r['sha256']
  extra={'known_construction_cases':12,'source_hashes':len(lock)}
 else:
  lock=json.loads((S/'scientific-freeze.json').read_text())
  for p,h in lock.items():assert sha(S/p)==h
  for name,needle in [('r47-discovery.md','Conjecture7.2'),('r34-discovery.md','599'),('r52-discovery.md','Question1.7')]:assert needle in (S/'history'/name).read_text()
  reg=json.loads((S/'sources/registry-receipt.json').read_text())
  assert reg['behind']==0 and reg['ahead']==reg['total_commits']==reg['commits_returned']==21 and reg['files_returned']==18 and not reg['api_cap_detected']
  assert not (S/'checks/results.json').exists()
  extra={'scientific_source_hashes':len(lock),'old_targets':3,'mathematical_search_executed':False}
 for r in m:assert sha(S/r['path'])==r['sha256']
 out[str(n)]={'manifest_entries':len(m),'integrity':'PASS','credit':0,**extra}
out['counts']=[9,39];out['qualification']='r128 copied finite controls only; r129 documentary integrity only. No universal proof or novelty clearance.'
(P/'ADOPTION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
