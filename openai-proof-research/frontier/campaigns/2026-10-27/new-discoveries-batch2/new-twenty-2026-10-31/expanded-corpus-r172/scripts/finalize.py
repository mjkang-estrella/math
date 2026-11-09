import pathlib,json,hashlib,datetime,collections,re
D=pathlib.Path(__file__).resolve().parents[1];B=D.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=[B/'ledger.json',D.parent/'ledger.json',B/'prior-campaign-context.json',D.parents[5]/'AGENTS.md',B/'AGENTS.md',D.parent/'AGENTS.md',B/'lanes/sol-fresh-source-discovery-r40/SUMMARY.md',B/'lanes/sol-fresh-source-discovery-r40/discovery.md']
receipts=[]
for p in paths:
 if p.exists():receipts.append({'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size})
(D/'outputs/history-receipts.json').write_text(json.dumps(receipts,indent=2))
o=json.loads((D.parent/'ledger.json').read_text());families=[]
for key,value in o.items():
 if isinstance(value,list):
  for x in value:
   if isinstance(x,dict) and any(k in x for k in ['title','reason','status']):families.append({'section':key,**{k:x[k] for k in ['title','mathdb_id','id','status','reason'] if k in x}})
(D/'outputs/inherited-families.json').write_text(json.dumps(families,indent=2,ensure_ascii=False))
print('new ledger fields',list(o)[:16]);print('families',len(families));print('\n'.join(str(x.get('title',x.get('id',''))) for x in families[:50]))
# Final IDs and raw hashes validate again after generation.
r=json.loads((D/'results.json').read_text());assert len(r)==20
for k,v in r.items():assert sha(D/'raw'/f'{k}.jsonl')==v['provenance']['raw_sha256']
assert (D/'outputs/validation.json').exists() and json.loads((D/'outputs/validation.json').read_text())['passed']
manifest=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name!='manifest.json' and '__pycache__' not in p.parts:manifest.append({'path':str(p.relative_to(D)),'sha256':sha(p),'bytes':p.stat().st_size})
(D/'manifest.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':manifest},indent=2))
print('manifest',len(manifest))
