import json,hashlib,pathlib
D=pathlib.Path(__file__).resolve().parents[1]; B=D.parent.parent
ids=set(json.loads((D/'reservation.json').read_text())['ids']); out={}
h=lambda b:hashlib.sha256(b).hexdigest()
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=p.read_bytes(); ch=h(data)
 for n,line in enumerate(data.splitlines(keepends=True),1):
  row=json.loads(line); i=row.get('id',row.get('mathdb_id'))
  if i in ids:
   (D/f'raw/{i}.jsonl').write_bytes(line)
   out[str(i)]={'chunk':str(p),'one_based_line':n,'chunk_sha256':ch,'raw_sha256':h(line),'row':row}
(D/'outputs/provenance.json').write_text(json.dumps(out,indent=2)+'\n')
for i,r in out.items(): print(i,json.dumps(r['row'],ensure_ascii=False))
