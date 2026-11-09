import json,hashlib
from pathlib import Path
L=Path(__file__).resolve().parents[1]; B=L.parent.parent; R=json.loads((L/'reservation.json').read_text()); ids=set(R['ids']); out={}; h=lambda x:hashlib.sha256(x).hexdigest()
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 chunkhash=h(p.read_bytes())
 for n,line in enumerate(p.open('rb'),1):
  if not any(str(i).encode() in line for i in ids): continue
  d=json.loads(line); i=d.get('mathdb_id',d.get('id'))
  if i in ids:
   (L/f'raw/{i}.jsonl').write_bytes(line); out[str(i)]={'chunk':str(p),'line':n,'chunk_sha256':chunkhash,'raw_sha256':h(line),'record':d}
(L/'outputs/exact-records.json').write_text(json.dumps(out,indent=2)); print(json.dumps(out,indent=2))
for p in [B/'ledger.json',B/'prior-campaign-context.json',L.parent/'ledger.json']:
 d=json.loads(p.read_text()); (L/f'outputs/context-{p.parent.name}-{p.name}').write_text(json.dumps(d,indent=2))
