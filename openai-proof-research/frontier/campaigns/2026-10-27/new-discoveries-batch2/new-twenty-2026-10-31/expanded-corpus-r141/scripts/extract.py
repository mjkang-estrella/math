import json,pathlib,hashlib
L=pathlib.Path.cwd(); root=L.parents[1].parent
ids=set(json.loads((L/'reservation.json').read_text())['ids']); found={}
corpus=L.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
for p in sorted(corpus.glob('mathdb-normalized-chunk-*.jsonl')):
 h=None
 for no,raw in enumerate(p.open('rb'),1):
  d=json.loads(raw); i=d.get('id',d.get('mathdb_id'))
  try:i=int(i)
  except:continue
  if i in ids:
   if h is None:h=hashlib.sha256(p.read_bytes()).hexdigest()
   (L/f'sources/{i}.raw.jsonl').write_bytes(raw)
   found[str(i)]={'chunk':str(p),'line':no,'chunk_sha256':h,'raw_sha256':hashlib.sha256(raw).hexdigest(),'record':d}
(L/'outputs/extracted.json').write_text(json.dumps(found,indent=2))
print('found',len(found))
for i,d in found.items():print(i,json.dumps(d['record'],ensure_ascii=False))
