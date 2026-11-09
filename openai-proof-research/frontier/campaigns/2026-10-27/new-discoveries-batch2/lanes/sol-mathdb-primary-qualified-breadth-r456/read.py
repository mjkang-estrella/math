from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent;B=L.parent
assert json.loads((L/'preflight.json').read_text())['status']=='PASS'
ids=json.loads((B/'root-mathdb-breadth-intake-r455/reserved-ids.json').read_text())['ids']
def excluded(o):
 s=set()
 if isinstance(o,dict):
  for k,v in o.items():
   if k=='mathdb_id' and isinstance(v,int):s.add(v)
   elif k in ['mathdb_ids','problem_ids'] and isinstance(v,list):s.update(x for x in v if isinstance(x,int))
   s.update(excluded(v))
 elif isinstance(o,list):
  for v in o:s.update(excluded(v))
 return s
for f in ['accepted-exclusions.json','historical-dispositions.json']:
 assert not set(ids)&excluded(json.loads((B/'root-mathdb-accepted-exclusions-r304'/f).read_text()))
found={}
for p in sorted((B/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for lineno,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   assert r['mathdb_id'] not in found
   found[r['mathdb_id']]=dict(record=r,original_chunk=str(p),original_line=lineno,statement_sha256=hashlib.sha256(r['statement'].encode()).hexdigest(),canonical_record_sha256=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest())
assert set(found)==set(ids)
(L/'records.json').write_text(json.dumps([found[i] for i in ids],ensure_ascii=False,indent=2)+'\n')
with (L/'statements.txt').open('w') as f:
 for i in ids:
  r=found[i]['record'];f.write(f"\n=== {i}: {r['title']} ===\n{r['statement']}\nSOURCE: {r['source_name']} | {r['source_url']}\nREFERENCES: {r['references']}\n")
print('50 records extracted; accepted/historical exclusion disjointness PASS')
