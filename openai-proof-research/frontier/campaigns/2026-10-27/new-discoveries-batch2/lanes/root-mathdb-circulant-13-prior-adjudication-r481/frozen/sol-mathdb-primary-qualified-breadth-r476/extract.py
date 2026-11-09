exec_prefix='' # No upstream code executed.
import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parent;L=D.parent;I=L/'root-mathdb-breadth-intake-r475';V=L/'pi-mathdb-full-corpus-inventory-r301'
h=lambda b:hashlib.sha256(b).hexdigest()
reserved=json.loads((I/'reserved-ids.json').read_text());ids=reserved['ids'];q=json.loads((I/'queue.json').read_text());coverage=json.loads((I/'coverage-delta.json').read_text())
assert len(ids)==len(set(ids))==50 and ids==[x['mathdb_id'] for x in q]
assert not set(ids)&set(reserved['other_active_reservations'])
assert not set(ids)&{int(x) for x in coverage};assert len(coverage)==3233
assert not set(ids)&{372627,372628,368940,404067,364119}
def assoc(o):
 if isinstance(o,dict):
  for k,v in o.items():
   if k in ('mathdb_id','mathdb_related_id','related_mathdb_id') and isinstance(v,int): yield v
   elif k in ('mathdb_ids','problem_ids','all_excluded_ids','excluded_ids') and isinstance(v,list):yield from (x for x in v if isinstance(x,int))
   else:yield from assoc(v)
 elif isinstance(o,list):
  for v in o:yield from assoc(v)
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 assert not set(ids)&set(assoc(json.loads((L/'root-mathdb-accepted-exclusions-r304'/n).read_text())))
rows=[];m=json.loads((V/'manifest.json').read_text())
for e in m['files']:
 if not e['path'].startswith('corpus/mathdb-normalized-chunk-'):continue
 p=V/e['path']
 for line,b in enumerate(p.open('rb'),1):
  r=json.loads(b)
  if r['mathdb_id'] in ids:
   rows.append({'record':r,'original_chunk':str(p),'original_line':line,'line_sha256':h(b),'statement_utf8_sha256':h(r['statement'].encode()),'canonical_record_sha256':h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())})
assert len(rows)==50 and len({x['record']['mathdb_id'] for x in rows})==50
rows.sort(key=lambda x:ids.index(x['record']['mathdb_id']))
(D/'assigned-records.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
with (D/'literal-statements.txt').open('w') as f:
 for x in rows:
  r=x['record'];f.write(f"\nID {r['mathdb_id']} {r['title']}\n{r['statement']}\nSOURCE {r['source_name']}\n{r['source_url']}\nREF {r['references']}\n")
print('PASS exact 50; baseline 3233; assignments and exclusions disjoint; originals extracted')
