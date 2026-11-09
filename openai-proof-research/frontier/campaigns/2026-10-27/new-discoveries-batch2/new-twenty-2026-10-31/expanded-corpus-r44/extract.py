import json,hashlib
from pathlib import Path
P=Path(__file__).resolve().parent;B=P.parent.parent; C=B/'lanes/pi-mathdb-full-corpus-inventory-r301'
h=lambda x:hashlib.sha256(x).hexdigest()
r=json.loads((P/'reservation.json').read_text());ids=set(r['ids']);out={};(P/'raw').mkdir(exist_ok=True)
for f in sorted((C/'corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=f.read_bytes();ch=h(data)
 for n,line in enumerate(data.splitlines(keepends=True),1):
  x=json.loads(line);i=int(x['mathdb_id'])
  if i in ids:
   (P/'raw'/f'{i}.jsonl').write_bytes(line);out[str(i)]={'chunk':str(f.resolve()),'line_1based':n,'chunk_sha256':ch,'raw_sha256':h(line),'statement_sha256':h(x['statement'].encode()),'record':x}
assert len(out)==40
(P/'literal-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
(P/'statements.txt').write_text('\n\n'.join(f"ID {i} {v['record']['title']}\n{v['record']['statement']}\nSOURCE: {v['record']['source_url']}\nREF: {v['record']['references']}" for i,v in out.items()))
print((P/'statements.txt').read_text())
