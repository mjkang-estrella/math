import pathlib,json,hashlib
O=pathlib.Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r431'
a=json.loads((I/'reserved-ids.json').read_text());ids=set(a['ids']);q=json.loads((I/'queue.json').read_text());base=json.loads((I/'coverage-delta.json').read_text())
assert len(ids)==50 and ids=={r['mathdb_id'] for r in q};assert len(base)==2183
assert not ids & ({int(k) for k in base}|set(a['other_active_reservations'])|{372627,372628,368940,404067,364119})
rs=[];loc=[]
for p in sorted((L/'pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   rs.append(r);loc.append({'mathdb_id':r['mathdb_id'],'original':str(p),'line':n,'statement_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_sha256':hashlib.sha256(json.dumps(r,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest()})
assert len(rs)==50
(O/'records.json').write_text(json.dumps(rs,ensure_ascii=False,indent=2)+'\n');(O/'record-locations.json').write_text(json.dumps(loc,indent=2)+'\n')
with (O/'literal-reading.txt').open('w') as f:
 for r in rs:f.write(f"\nID {r['mathdb_id']} {r['title']}\n{r['statement']}\nSOURCE {r['source_name']} {r['source_url']}\nREFERENCES {r['references']}\n")
print((O/'literal-reading.txt').read_text())
