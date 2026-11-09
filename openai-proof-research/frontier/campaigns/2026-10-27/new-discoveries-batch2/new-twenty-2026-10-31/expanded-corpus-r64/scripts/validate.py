import json,pathlib,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((D/'reservation.json').read_text());x=json.loads((D/'results.json').read_text());assert set(x)=={str(i) for i in r['ids']} and len(x)==40
chunks={};checked=0
for i,o in x.items():
 p=o['provenance'];raw=(D/f'raw/{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert sha(raw)==p['raw_sha256'];assert sha(o['statement'].encode())==p['statement_utf8_sha256'];assert json.loads(raw)['statement']==o['statement']
 path=pathlib.Path(p['chunk'])
 if path not in chunks:chunks[path]=path.read_bytes();assert sha(chunks[path])==p['chunk_sha256']
 assert chunks[path].splitlines(keepends=True)[p['line_1based']-1]==raw
 src=D/o['source_receipt'].removesuffix('.receipt.json');receipt=json.loads((D/o['source_receipt']).read_text());assert sha(src.read_bytes())==receipt['sha256']==o['source_sha256'];assert receipt['status']==200
 assert o['lean_endpoint'] is None and o['credit']==0;checked+=1
source_receipts=list((D/'sources').glob('*.receipt.json'))
for p in source_receipts:
 o=json.loads(p.read_text())
 if 'sha256' in o:assert sha(pathlib.Path(o['path']).read_bytes())==o['sha256']
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exact_id_count':checked,'raw_line_and_chunk_hashes_verified':True,'receipt_hashes_verified':len(source_receipts),'claimed_endpoints':0,'claimed_credit':0,'campaign_count_changed':False,'lean_checks':'not applicable: no full literal endpoint claimed','background_processes':'All launched fetch/diagnostic processes completed; no background job created for handback.'}
(D/'outputs/validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
manifest={str(p.relative_to(D)):sha(p.read_bytes()) for p in sorted(D.rglob('*')) if p.is_file() and '__pycache__' not in str(p) and p.name!='manifest.json'}
(D/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
