from pathlib import Path
import json,hashlib,datetime
O=Path(__file__).resolve().parent
terms=['2610.26535','rank score veto','rank-score veto','2507.17981','2307.07495','2305.19632','2610.24456','2608.26854','2608.21790','2608.21202','2608.17863','2502.10068','1911.08129']
rows=[];hits=[];fail=[]
for name in ['4-qualified-original-index.json','5-inherited-aliases.json']:
 for r in json.loads((O/'frozen'/name).read_text())['records']:
  p=Path(r['snapshot_reference']);expected=r['sha256']
  try:
   data=p.read_bytes();h=hashlib.sha256(data).hexdigest()
   rows.append({'path':str(p),'expected':expected,'sha256':h})
   if h!=expected:fail.append({'path':str(p),'error':'hash mismatch'})
   text=data.decode(errors='replace').lower();found=[t for t in terms if t.lower() in text]
   if found:hits.append({'path':str(p),'terms':found})
  except Exception as e:fail.append({'path':str(p),'error':str(e)})
(O/'history-screen.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'references':rows,'hits':hits,'failures':fail,'limit':'inherited verified references only; no parked historical intervals reopened; current mutable discoveries not comprehensively scanned'},indent=2))
print('references',len(rows),'hits',hits,'failures',len(fail))
