import pathlib,json,hashlib,zipfile
D=pathlib.Path(__file__).resolve().parents[1];rows=json.loads((D/'extracted.json').read_text());results=json.loads((D/'results.json').read_text());ids=set(map(str,json.loads((D/'reservation.json').read_text())['ids']));assert set(results)==ids and len(ids)==20
for i,r in rows.items():
 raw=(D/'raw'/(i+'.jsonl')).read_bytes();assert raw.endswith(b'\n');o=json.loads(raw)
 assert hashlib.sha256(raw).hexdigest()==r['provenance']['raw_sha256']
 assert hashlib.sha256(o['statement'].encode()).hexdigest()==r['provenance']['statement_utf8_sha256']
 assert results[i]['statement']==o['statement']
assert all(x['accepted_credit']==0 for x in results.values())
reg=json.loads((D/'outputs/registry-screen.json').read_text());assert set(reg['by_id'])==ids
with zipfile.ZipFile(D/'Lean-packet.zip') as z:
 m=json.loads(z.read('packet-manifest.json'))
 for p,h in m['files'].items():assert hashlib.sha256(z.read(p)).hexdigest()==h,p
 assert z.testzip() is None
for f in ['lean-plane-r2','lean-fresh','leanchecker-aux-r2','lrat-independent']:
 assert json.loads((D/'logs'/(f+'.receipt.json')).read_text())['returncode']==0
manifest={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in D.rglob('*') if p.is_file() and p.name!='file-manifest.json'}
(D/'outputs/file-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Validated20 exact raw records; candidate packet hashes; successful auxiliary Lean/replay/leanchecker and independent RUP receipts. Full target theorem remains unproved in Lean.')
