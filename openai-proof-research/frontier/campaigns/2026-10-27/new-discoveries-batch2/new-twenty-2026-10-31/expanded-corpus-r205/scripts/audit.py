import pathlib,json,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text());reservation=json.loads((D/'reservation.json').read_text());assert set(map(int,r))==set(reservation['ids']);fail=[];receipts=list((D/'sources').glob('*/receipt.json'))
for p in receipts:
 o=json.loads(p.read_text());b=p.parent/'body'
 if 'sha256' in o:assert hashlib.sha256(b.read_bytes()).hexdigest()==o['sha256'],str(p)
for i,o in r.items():
 assert hashlib.sha256((D/f'raw/{i}.jsonl').read_bytes()).hexdigest()==o['provenance']['raw_sha256']
 assert hashlib.sha256(o['statement'].encode()).hexdigest()==o['provenance']['statement_utf8_sha256']
 o['source_body_bindings']=[{'receipt':str(p.relative_to(D)),'sha256':json.loads(p.read_text()).get('sha256'),'status':json.loads(p.read_text()).get('status')} for p in receipts if i in p.parent.name]
(D/'results.json').write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n')
# Named artifact hashes; manifest does not include itself.
files=['results.json','SUMMARY.md','CANDIDATE.md','extracted.json','outputs/registry-screen.json','outputs/http-manifest.json']
a={'id_count':len(r),'http_receipt_count':len(receipts),'raw_bindings_verified':20,'accepted_credit':0,'lean_packet':'Not applicable: no qualifying endpoint','artifacts':{s:hashlib.sha256((D/s).read_bytes()).hexdigest() for s in files},'resource_logs':{p.stem:json.loads(p.read_text()) for p in (D/'logs').glob('*.json')}}
(D/'outputs/audit.json').write_text(json.dumps(a,indent=2));print(json.dumps({k:v for k,v in a.items() if k!='resource_logs'},indent=2))
