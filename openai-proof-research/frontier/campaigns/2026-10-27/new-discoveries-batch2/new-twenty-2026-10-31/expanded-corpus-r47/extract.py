import json,hashlib,pathlib,subprocess,datetime
out=pathlib.Path(__file__).resolve().parent;b=out.parent.parent; ids=json.loads((out/'reservation.json').read_text())['ids'];(out/'raw').mkdir(exist_ok=True); res={}
for p in sorted((b/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=p.read_bytes();ch=hashlib.sha256(data).hexdigest()
 for n,line in enumerate(data.splitlines(keepends=True),1):
  d=json.loads(line);i=d.get('mathdb_id')
  if i in ids:
   (out/'raw'/f'{i}.jsonl').write_bytes(line);res[str(i)]={'record':d,'provenance':{'chunk':str(p),'line_1_based':n,'chunk_sha256':ch,'raw_sha256':hashlib.sha256(line).hexdigest(),'statement_sha256':hashlib.sha256(d['statement'].encode()).hexdigest()}}
(out/'extracted.json').write_text(json.dumps(res,indent=2));assert len(res)==40
with (out/'statements.txt').open('w') as f:
 for i in map(str,ids):
  d=res[i]['record'];f.write(f"\n{i} {d['title']}\n{d['statement']}\nSOURCE {d['source_name']} {d['source_url']}\n")
