import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent; B=L.parent.parent; R=json.loads((L/'reservation.json').read_text()); ids=set(R['ids']); out={}
(L/'raw').mkdir(exist_ok=True)
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 for n,line in enumerate(p.open('rb'),1):
  x=json.loads(line)
  if x['mathdb_id'] in ids:
   i=str(x['mathdb_id']);(L/'raw'/f'{i}.jsonl').write_bytes(line)
   out[i]={'chunk':str(p),'line':n,'chunk_sha256':h,'raw_sha256':hashlib.sha256(line).hexdigest(),'statement_sha256':hashlib.sha256(x['statement'].encode()).hexdigest(),'record':x}
assert len(out)==40
(L/'extracted.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
for i,x in out.items():
 r=x['record'];print(i,r['title'],'\n',r['statement'],'\nSOURCE',r['source_name'],r['source_url'],'\n')
