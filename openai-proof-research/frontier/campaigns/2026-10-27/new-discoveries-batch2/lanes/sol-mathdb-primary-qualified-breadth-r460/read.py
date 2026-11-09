import json,pathlib,hashlib
L=pathlib.Path(__file__).resolve().parent;B=L.parent
ids=set(json.loads((B/'root-mathdb-breadth-intake-r459/reserved-ids.json').read_text())['ids']);rows=[]
for p in sorted((B/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl')):
 for line,b in enumerate(p.open('rb'),1):
  r=json.loads(b)
  if r['mathdb_id'] in ids:
   rows.append({'record':r,'original_chunk':str(p),'original_line':line,'line_sha256':hashlib.sha256(b).hexdigest(),'statement_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(rows)==50 and {r['record']['mathdb_id'] for r in rows}==ids
(L/'records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
with (L/'statements.txt').open('w') as o:
 for x in rows:
  r=x['record'];o.write(f"\n=== {r['mathdb_id']} {r['title']} ===\n{r['statement']}\nSOURCE {r.get('source_url')}\n{r.get('source_name')}\nREF {r.get('references')}\n")
print('50 literal records extracted')
