from pathlib import Path
import json,re,hashlib,datetime
O=Path(__file__).resolve().parent;B=O.parents[1];R=B/'lanes/root-edge-irregulator-current-prior-r1'
pat=re.compile(r'silicos|1901[._-]?10670|2109[._-]?01172|pinelis|descartes|variation.?dimin|total.?posit|rational.?prod|equilib',re.I)
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'freshness':'Reuse of root complete inventories observed 2026-10-29T17:20:12Z, not new HEAD requests','trees':{},'context':{}}
for n,expected in [('omega-tree.txt','f9720a055ed0ff83150a53e903f870543582f1a86ed1ba7cca53b1fa81296ec0'),('openai-tree.txt','00170dce8bd5fe393656413fede0f983fcd8d400c84d90c3154e838c7cd74134')]:
 h=hashlib.sha256();hits=[];count=0
 with (R/n).open('rb') as f:
  for line in f:
   h.update(line);count+=1
   s=line.decode();
   if pat.search(s):hits.append(s.strip())
 assert h.hexdigest()==expected
 out['trees'][n]=dict(sha256=h.hexdigest(),entries=count,hits=hits)
for n in ['context-ledger.json','context-prior-campaign-context.json']:
 j=json.loads((O/n).read_text());entries=[]
 for key,val in j.items():
  if isinstance(val,list):
   for item in val:
    entries.append({'section':key,'item':item})
 out['context'][n]=dict(sha256=hashlib.sha256((O/n).read_bytes()).hexdigest(),counts={k:v for k,v in j.items() if 'count' in k},entries=entries)
(O/'screen.json').write_text(json.dumps(out,indent=2))
print(json.dumps({n:{'entries':r['entries'],'hits':len(r['hits']),'sample':r['hits'][:12]} for n,r in out['trees'].items()},indent=2))
for n,r in out['context'].items():
 print(n,r['counts'])
 for e in r['entries']:
  v=e['item'];print(e['section'], str(v.get('title',v.get('name',v.get('status',''))))[:180] if isinstance(v,dict) else str(v)[:180])
