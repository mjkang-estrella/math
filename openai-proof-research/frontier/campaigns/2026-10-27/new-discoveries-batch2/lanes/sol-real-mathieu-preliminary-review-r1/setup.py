from pathlib import Path
import json,hashlib,shutil,datetime
L=Path(__file__).resolve().parent; B=L.parent.parent
f=json.loads((B/'lanes/root-fresh-source-r51-handback/review-freeze.json').read_text()); out=[]
for name,v in f['files'].items():
 p=Path(f['lane'])/name; data=p.read_bytes(); h=hashlib.sha256(data).hexdigest(); assert h==v['sha256'] and len(data)==v['bytes'],name
 q=L/'frozen'/name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data);out.append({'path':name,'sha256':h,'bytes':len(data)})
(L/'freeze-before.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'binding_commit':'5ef31e68f5c765aa3c28b9e403415736fed6a47e','verified':out},indent=2))
for n in ['ledger.json','prior-campaign-context.json','AGENTS.md']:shutil.copy2(B/n,L/('context-'+n))
