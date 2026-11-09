import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1];B=D.parent.parent
for name,p in [('ledger',D.parent/'ledger.json'),('batch-ledger',B/'ledger.json'),('prior',B/'prior-campaign-context.json')]:
 data=p.read_bytes();(D/'logs'/f'{name}.json').write_bytes(data)
 print(name,hashlib.sha256(data).hexdigest(),len(data))
x=json.loads((D/'reservation.json').read_text());papers=sorted(set(r['source_url'].rsplit('/',1)[1] for r in x['rows']))
(D/'sources-plan.json').write_text(json.dumps([(a+'.html','https://arxiv.org/html/'+a) for a in papers]))
