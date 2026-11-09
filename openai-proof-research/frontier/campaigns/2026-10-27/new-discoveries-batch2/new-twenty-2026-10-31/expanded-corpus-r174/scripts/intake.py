import pathlib,json,hashlib
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
B=L.parent.parent
ids=set(json.loads((L/'reservation.json').read_text())['ids'])
out={}
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 with p.open('rb') as f:
  for ln,raw in enumerate(f,1):
   # Fast screen before JSON decode.
   if not any(str(i).encode() in raw for i in ids):continue
   d=json.loads(raw);i=d.get('id',d.get('mathdb_id'))
   if i is None:continue
   i=int(i)
   if i not in ids:continue
   (L/f'raw/{i}.jsonl').write_bytes(raw)
   out[str(i)]={'chunk':str(p),'line':ln,'chunk_sha256':h,'raw_sha256':hashlib.sha256(raw).hexdigest(),'record':d}
(L/'outputs/intake.json').write_text(json.dumps(out,indent=2))
for i,d in out.items():print(i,json.dumps(d['record'],ensure_ascii=False))
for p in [B/'ledger.json',B/'prior-campaign-context.json',L.parent/'ledger.json']:
 d=json.loads(p.read_text())
 (L/'outputs'/('context-'+p.parent.name+'-'+p.name)).write_text(json.dumps(d,indent=2))
 print('CONTEXT',p, list(d) if isinstance(d,dict) else len(d))
