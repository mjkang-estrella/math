import pathlib,json,hashlib
L=pathlib.Path(__file__).parent; B=L.parent
hits=[]
for f in sorted((B.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=f.read_bytes()
 for n,line in enumerate(data.splitlines(keepends=True),1):
  if not any(('"mathdb_id": '+i).encode() in line for i in ['330264','352038','324342']):continue
  r=json.loads(line); i=str(r['mathdb_id'])
  if i not in ['330264','352038','324342']:continue
  (L/(i+'.raw.jsonl')).write_bytes(line)
  hits.append(dict(id=i,path=str(f),line=n,chunk_sha256=hashlib.sha256(data).hexdigest(),line_sha256=hashlib.sha256(line).hexdigest(),record=r))
(L/'literal-bindings.json').write_text(json.dumps(hits,indent=2))
assert len(hits)==3
for r in hits: print(r['id'],r['line'],r['record']['statement'])
