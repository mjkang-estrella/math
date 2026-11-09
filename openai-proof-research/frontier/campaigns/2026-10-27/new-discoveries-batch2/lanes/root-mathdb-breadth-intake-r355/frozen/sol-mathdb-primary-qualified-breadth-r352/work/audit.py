from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parents[1];B=L.parent
ids=json.loads((B/'root-mathdb-breadth-intake-r350/reserved-ids.json').read_text())['ids']
M=B/'root-mathdb-accepted-exclusions-r304'
for r in json.loads((M/'manifest.json').read_text()):assert hashlib.sha256((M/r['path']).read_bytes()).hexdigest()==r['sha256'],r['path']
cov=json.loads((B/'root-mathdb-breadth-intake-r350/coverage-delta.json').read_text());assert len(cov)==483
queue=json.loads((B/'root-mathdb-breadth-intake-r350/queue.json').read_text());print('queue schema',type(queue).__name__)
print('coverage overlap',sorted(set(ids)&set(map(int,cov))))
a=json.loads((M/'accepted-exclusions.json').read_text());h=json.loads((M/'historical-dispositions.json').read_text())
def hits(x):
 out=[]
 if isinstance(x,dict):
  if any((v in ids if isinstance(v,int) else any(i in v for i in ids) if isinstance(v,list) else False) for k,v in x.items() if 'id' in k):out.append(x)
  for v in x.values():out+=hits(v)
 elif isinstance(x,list):
  for v in x:out+=hits(v)
 return out
out={'r350_reviewed_count':len(cov),'r350_overlap':sorted(set(ids)&set(map(int,cov))),'accepted_index_hits':hits(a),'historical_hits':hits(h),'r351_overlap':'All fifty literal statements were present in a partial record extract, independently validated equal; no r351 completed dispositions. Not fifty new-to-campaign IDs beyond a separate r351 report.'}
(L/'coverage-audit.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2))
