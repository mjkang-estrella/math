from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parents[1];B=L.parent
ids=list(map(str,json.loads((B/'root-mathdb-breadth-intake-r355/reserved-ids.json').read_text())['ids']))
coverage=json.loads((B/'root-mathdb-breadth-intake-r355/coverage-delta.json').read_text());assert len(coverage)==533
queue=json.loads((B/'root-mathdb-breadth-intake-r355/queue.json').read_text()); assert len(ids)==len(set(ids))==50 and set(ids)=={str(x['mathdb_id']) for x in queue}
assert not set(ids)&set(coverage) and not set(ids)&{'364119','404067'}
ex=json.loads((B/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json').read_text()); hist=json.loads((B/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json').read_text())
def ids_in(x):
 out=set()
 if isinstance(x,dict):
  for k,v in x.items():
   if k=='mathdb_id':out.add(str(v))
   elif k in ['mathdb_ids','problem_ids']:out.update(map(str,v))
   else:out|=ids_in(v)
 elif isinstance(x,list):
  for v in x:out|=ids_in(v)
 return out
assert not set(ids)&ids_in(ex)
audit={'reserved':50,'prior_coverage':533,'coverage_overlap':[],'accepted_overlap':[],'historical_overlap':sorted(set(ids)&ids_in(hist)),'potential_union':583}
(L/'coverage-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
found={}
for p in sorted((B/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 with p.open() as f:
  for ln,line in enumerate(f,1):
   r=json.loads(line);n=str(r['mathdb_id'])
   if n in ids:
    assert n not in found
    r['corpus_path']=str(p);r['corpus_line']=ln;r['literal_statement_sha256']=hashlib.sha256(r['statement'].encode()).hexdigest();found[n]=r
assert set(found)==set(ids)
rows=[found[n] for n in ids];(L/'records.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
for r in rows:
 print('\nID',r['mathdb_id'],r['title'],'\n'+r['statement']+'\nSOURCE '+str(r['source_url']))
print('AUDIT',audit)
