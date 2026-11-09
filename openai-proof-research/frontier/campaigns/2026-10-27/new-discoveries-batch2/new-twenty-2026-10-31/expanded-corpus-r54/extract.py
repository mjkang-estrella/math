import pathlib,json,hashlib,re,subprocess
D=pathlib.Path(__file__).resolve().parent; P=D.parent; B=P.parent
h=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((D/'reservation.json').read_text()); ids=set(r['ids']); out={}; (D/'raw').mkdir(exist_ok=True)
C=B/'lanes/pi-mathdb-full-corpus-inventory-r301'
for f in sorted((C/'corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=f.read_bytes(); ch=h(data)
 for n,line in enumerate(data.splitlines(keepends=True),1):
  o=json.loads(line); i=o.get('mathdb_id',o.get('id'))
  if i in ids:
   (D/'raw'/f'{i}.jsonl').write_bytes(line);out[str(i)]={'chunk':str(f),'line_1based':n,'chunk_sha256':ch,'raw_sha256':h(line),'record':o}
(D/'exact-records.json').write_text(json.dumps(out,indent=2))
print('found',len(out));print('keys',next(iter(out.values()))['record'].keys())
for i,o in out.items():
 print(i,json.dumps(o['record'],ensure_ascii=False))
