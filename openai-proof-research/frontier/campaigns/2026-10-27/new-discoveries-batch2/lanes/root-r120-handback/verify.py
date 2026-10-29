from pathlib import Path
import json,hashlib,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r120'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
m=json.loads((S/'finalmanifest.json').read_text())['files']
for k,v in m.items():assert sha(S/k)==v['sha256'] and (S/k).stat().st_size==v['bytes'],k
lock=json.loads((S/'source-lock.json').read_text())
for row in lock:assert sha(S/row['path'])==row['sha256'],row['path']
shutil.copy2(S/'checks.py',P/'copied-checks.py');shutil.copy2(S/'http.jsonl',P/'http.jsonl')
for line in (P/'http.jsonl').read_text().splitlines():
 r=json.loads(line)
 if 'copy' in r:
  dest=P/r['copy'];dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(S/r['copy'],dest)
run=subprocess.run([sys.executable,str(P/'copied-checks.py')],capture_output=True,text=True,check=True)
(P/'checks.log').write_text(run.stdout+run.stderr)
j=json.loads((P/'checks.json').read_text());assert j['status']=='PASS' and j['orders_checked']==13 and not j['all_order_proof']
for k,v in m.items():assert sha(S/k)==v['sha256'],k
out={'status':'PASS','manifest_entries':len(m),'frozen_source_hashes':len(lock),'copied_checker_sha256':sha(P/'copied-checks.py'),'exact_orders_checked':13,'credit':0,'counts':[9,39],'qualification':'Copied checker replay, not an independent implementation. Root independently checked the ordinary IBP and endpoint-bound argument; not a full audit of every public paper result.'}
(P/'ADOPTION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
