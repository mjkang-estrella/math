import pathlib,json,hashlib,collections
D=pathlib.Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((D/'results.json').read_text());ids=set(json.loads((D/'reservation.json').read_text())['ids']);assert set(map(int,r))==ids and len(r)==20
for k,o in r.items():
 p=D/f'raw/{k}.jsonl';raw=p.read_bytes();assert raw.endswith(b'\n') and sha(p)==o['provenance']['raw_sha256'];d=json.loads(raw);assert d['statement']==o['literal_statement'];assert hashlib.sha256(d['statement'].encode()).hexdigest()==o['provenance']['statement_sha256'];assert o['credit']==0 and o['lean_endpoint'] is None
for p in (D/'sources').glob('*.receipt.json'):
 x=json.loads(p.read_text());body=p.with_name(p.name.removesuffix('.receipt.json'))
 if x.get('sha256'):assert body.is_file() and sha(body)==x['sha256'],p
out={'entries':len(r),'excluded':sum(o['outcome'].startswith('excluded') for o in r.values()),'parked':sum(o['outcome'].startswith('parked') for o in r.values()),'http_receipts_verified':len(list((D/'sources').glob('*.receipt.json'))),'credit':0,'all_raw_and_statement_hashes_verified':True}
(D/'outputs/packet-validation.json').write_text(json.dumps(out,indent=2));print(out)
manifest={str(p.relative_to(D)):sha(p) for p in sorted(D.rglob('*')) if p.is_file() and p.name!='manifest.json'}
(D/'manifest.json').write_text(json.dumps(manifest,indent=2))
