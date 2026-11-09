import pathlib,json,hashlib
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r186')
B=L.parent.parent
ids=set(json.loads((L/'reservation.json').read_text())['ids'])
manifest={}
for p in sorted((B/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 data=p.read_bytes(); ch=hashlib.sha256(data).hexdigest()
 for num,line in enumerate(data.splitlines(keepends=True),1):
  r=json.loads(line); i=r.get('mathdb_id',r.get('id'))
  if i and int(i) in ids:
   (L/f'sources/{i}.raw.jsonl').write_bytes(line)
   manifest[str(i)]={'chunk':str(p),'line':num,'chunk_sha256':ch,'raw_sha256':hashlib.sha256(line).hexdigest(),'statement_sha256':hashlib.sha256(r.get('statement','').encode()).hexdigest()}
   print(i,json.dumps(r,ensure_ascii=False))
(L/'outputs/provenance.json').write_text(json.dumps(manifest,indent=2))
for p in [B/'ledger.json',B/'prior-campaign-context.json',L.parent/'ledger.json']:
 d=p.read_bytes(); obj=json.loads(d); print('CONTEXT',str(p),len(d),list(obj)[:15])
 (L/('outputs/context-'+p.parent.name+'-'+p.name)).write_bytes(d)
