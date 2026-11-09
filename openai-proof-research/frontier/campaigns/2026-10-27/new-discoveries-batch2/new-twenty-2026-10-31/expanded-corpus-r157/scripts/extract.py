import json,pathlib,hashlib
lane=pathlib.Path.cwd(); ids=set(json.loads((lane/'reservation.json').read_text())['ids']); out={}
corpus=lane.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
for f in sorted(corpus.glob('mathdb-normalized-chunk-*.jsonl')):
 found=[]
 for n,line in enumerate(f.open('rb'),1):
  r=json.loads(line); i=r.get('id',r.get('mathdb_id'))
  if i not in ids:continue
  (lane/'raw'/f'{i}.jsonl').write_bytes(line)
  out[str(i)]={'chunk':str(f),'line_1based':n,'raw_sha256':hashlib.sha256(line).hexdigest(),'record':r};found.append(i)
 if found:
  h=hashlib.sha256()
  with f.open('rb') as src:
   for b in iter(lambda:src.read(1048576),b''):h.update(b)
  for i in found:out[str(i)]['chunk_sha256']=h.hexdigest()
(lane/'outputs/provenance.json').write_text(json.dumps(out,indent=2))
for i,r in out.items():print(i,json.dumps(r['record'],ensure_ascii=False))
