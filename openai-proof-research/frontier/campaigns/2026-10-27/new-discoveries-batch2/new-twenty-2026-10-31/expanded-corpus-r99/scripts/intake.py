import pathlib,json,hashlib,datetime,re
L=pathlib.Path.cwd(); B=L.parent.parent
H=lambda x:hashlib.sha256(x).hexdigest()
r=json.loads((L/'reservation.json').read_text()); ids=set(r['ids']); found={}
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 chunkhash=H(p.read_bytes())
 for n,line in enumerate(p.open('rb'),1):
  j=json.loads(line); i=j.get('mathdb_id',j.get('id'))
  if i in ids:
   (L/f'raw/{i}.jsonl').write_bytes(line)
   found[str(i)]={'chunk':str(p),'line':n,'chunk_sha256':chunkhash,'raw_sha256':H(line),'record':j}
(L/'outputs/intake.json').write_text(json.dumps(found,indent=2))
for i,j in found.items():print(i,json.dumps(j['record'],ensure_ascii=False))
for p in [B/'ledger.json',B/'prior-campaign-context.json',L.parent/'ledger.json']:
 if p.exists():
  j=json.loads(p.read_text());print('CONTEXT',p, json.dumps(j)[:24000]);
