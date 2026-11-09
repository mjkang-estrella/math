import pathlib,json,hashlib
D=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166')
ids=set(json.loads((D/'reservation.json').read_text())['ids']); out={}
for p in (D.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus').glob('*.jsonl'):
 chunkhash=None
 for i,line in enumerate(p.open('rb'),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   if chunkhash is None: chunkhash=hashlib.sha256(p.read_bytes()).hexdigest()
   mid=str(r['mathdb_id']);(D/f'raw/{mid}.jsonl').write_bytes(line)
   out[mid]={'record':r,'chunk':str(p),'line':i,'chunk_sha256':chunkhash,'raw_sha256':hashlib.sha256(line).hexdigest(),'statement_sha256':hashlib.sha256(r['statement'].encode()).hexdigest()}
(D/'outputs/extraction.json').write_text(json.dumps(out,indent=2))
for mid,x in out.items():print(mid,x['record']['title'],'\n',x['record']['statement'],'\nSOURCE',x['record']['source_name'],'\n')
for rel in ['../ledger.json','../../ledger.json','../../prior-campaign-context.json']:
 p=D/rel;j=json.loads(p.read_text());print('LEDGER',rel,'keys',list(j));
 (D/('outputs/'+p.parent.name+'-'+p.name)).write_text(json.dumps(j,indent=2))
