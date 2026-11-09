import json,pathlib,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();R=json.loads((D/'results.json').read_text());reserved=json.loads((D/'reservation.json').read_text())['ids'];assert set(R)==set(map(str,reserved)) and len(R)==20
for i,r in R.items():
 b=(D/'raw'/f'{i}.jsonl').read_bytes();assert b.endswith(b'\n') and sha(b)==r['provenance']['raw_sha256'];assert sha(r['statement'].encode())==r['provenance']['statement_utf8_sha256'];assert json.loads(b)['statement']==r['statement'];assert r['credit']==0 and r['lean_endpoint'] is None
receipts=[]
for p in sorted((D/'http').glob('*.receipt.json')):
 r=json.loads(p.read_text());q=pathlib.Path(r.get('path',''))
 if 'sha256' in r:assert q.is_file() and sha(q.read_bytes())==r['sha256']
 receipts.append({'receipt':str(p.relative_to(D)),'sha256':sha(p.read_bytes()),'url':r['url'],'status':r.get('status'),'error':r.get('error')})
(D/'outputs/http-receipts-index.json').write_text(json.dumps(receipts,indent=2)+'\n')
manifest=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name!='artifact-manifest.json':manifest.append({'path':str(p.relative_to(D)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())})
(D/'outputs/artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'reserved_ids':20,'validated_raw_records':len(R),'validated_http_receipts':len(receipts),'excluded':sum(r['outcome'].startswith('excluded') for r in R.values()),'parked':sum(r['outcome'].startswith('parked') for r in R.values()),'new_endpoints':0,'manifest_files':len(manifest),'all_checks':'PASS'}))
