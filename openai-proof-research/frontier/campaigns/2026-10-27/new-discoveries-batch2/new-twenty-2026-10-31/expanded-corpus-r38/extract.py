from pathlib import Path
import json, hashlib
HERE=Path(__file__).resolve().parent
B=HERE.parent.parent
C=B/'lanes/pi-mathdb-full-corpus-inventory-r301'
h=lambda x:hashlib.sha256(x).hexdigest()
r=json.loads((HERE/'reservation.json').read_text()); ids=set(r['ids']); manifest=json.loads((C/'manifest.json').read_text()); out={}
(HERE/'raw').mkdir(exist_ok=True)
for e in manifest['files']:
 if not e['path'].startswith('corpus/mathdb-normalized-chunk-'):continue
 p=C/e['path']; data=p.read_bytes(); assert h(data)==e['sha256']
 for n,line in enumerate(data.splitlines(keepends=True),1):
  d=json.loads(line)
  if d['mathdb_id'] not in ids:continue
  i=str(d['mathdb_id']); (HERE/'raw'/f'{i}.jsonl').write_bytes(line)
  out[i]={'record':d,'provenance':{'chunk':str(p),'one_based_line':n,'chunk_sha256':h(data),'raw_line_sha256':h(line),'statement_utf8_sha256':h(d['statement'].encode()),'newline_preserved':line.endswith(b'\n')}}
assert len(out)==40
(HERE/'extracted.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
for i,e in out.items():print('\n###',i,e['record']['title'],'\n',e['record']['statement'],'\nSOURCE',e['record']['source_url'],e['record']['source_name'])
