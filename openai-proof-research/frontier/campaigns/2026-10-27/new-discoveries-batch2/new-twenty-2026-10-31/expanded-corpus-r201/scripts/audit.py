import pathlib,json,hashlib,collections
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert set(r)==set(map(str,ids)) and len(r)==20
for i,x in r.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n') and sha(b)==x['provenance']['raw_sha256'];o=json.loads(b);assert o['statement']==x['literal_statement'];assert sha(o['statement'].encode())==x['provenance']['statement_utf8_sha256'];assert x['accepted_credit']==0
receipts=[]
for p in (D/'sources').glob('*/receipt.json'):
 x=json.loads(p.read_text());b=pathlib.Path(x['body']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'];receipts.append(x)
reg=json.loads((D/'outputs/registry-screen.json').read_text());assert len(reg['queries'])==8;assert all(q['receipt']['status']==200 for q in reg['queries']);assert len(reg['per_id_pool_screen'])==20
cover=json.loads((D/'outputs/bruhat-coverage.json').read_text());assert not any(x['counterexamples'] for x in cover.values())
res={'ids':20,'raw_hashes_verified':20,'HTTP_receipts_verified':len(receipts),'HTTP_statuses':dict(collections.Counter(str(x['status']) for x in receipts)),'queries':8,'accepted_credit':0,'new_Lean_files':len(list(D.rglob('*.lean'))),'coverage':{n:{k:v for k,v in x.items() if k not in ['indices','counterexamples']} for n,x in cover.items()},'resource_receipts':len(list((D/'logs').glob('*.receipt.json'))),'qualification':'artifact and bounded computation checks only; no discovery or global novelty assertion'}
(D/'outputs/artifact-audit.json').write_text(json.dumps(res,indent=2));print(json.dumps(res,indent=2))
manifest={str(p.relative_to(D)):sha(p.read_bytes()) for p in D.rglob('*') if p.is_file() and '__pycache__' not in str(p) and p.name!='artifact-manifest.json'}
(D/'outputs/artifact-manifest.json').write_text(json.dumps(manifest,indent=2))
