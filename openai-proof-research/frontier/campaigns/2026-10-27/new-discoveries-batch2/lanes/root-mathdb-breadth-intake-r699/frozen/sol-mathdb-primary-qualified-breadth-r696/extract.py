import json,pathlib,hashlib
O=pathlib.Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r695';R=L/'pi-mathdb-full-corpus-inventory-r301'
q=json.loads((I/'queue-r696.json').read_text());ids={r['mathdb_id'] for r in q};assert len(ids)==50
out=[]
for f in sorted((R/'corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 with f.open() as h:
  for n,line in enumerate(h,1):
   r=json.loads(line)
   if int(r.get('id',r.get('mathdb_id',-1))) in ids:
    out.append(dict(record=r,chunk=str(f),line=n,canonical_record_sha256=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),line_sha256=hashlib.sha256(line.encode()).hexdigest()))
assert len(out)==50
(O/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print('record keys',out[0]['record'].keys())
for r in out:print(json.dumps(r['record'],ensure_ascii=False))
