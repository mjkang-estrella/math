import pathlib,json,hashlib,os
D=pathlib.Path(__file__).resolve().parents[1];rs=json.loads((D/'results.json').read_text());ids=set(json.loads((D/'reservation.json').read_text())['ids']);assert set(map(int,rs))==ids and len(rs)==20
for i,x in rs.items():
 b=(D/x['provenance']['raw_file']).read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==x['provenance']['raw_sha256'];assert hashlib.sha256(x['statement'].encode()).hexdigest()==x['provenance']['statement_utf8_sha256'];assert x['discovery_credit']==0 and x['lean_endpoint'] is None
receipts=list((D/'sources').glob('*.receipt.json'));bad=[]
for p in receipts:
 r=json.loads(p.read_text());b=p.with_name(p.name.replace('.receipt.json','.body'))
 if r.get('sha256') and (not b.exists() or hashlib.sha256(b.read_bytes()).hexdigest()!=r['sha256']):bad.append(str(p))
assert not bad
live=[]
for p in pathlib.Path('/proc').glob('[0-9]*/cmdline'):
 try:
  args=p.read_bytes().split(b'\0')
  if any(a.endswith(b'/modular.py') or a.endswith(b'/flows.py') or a.endswith(b'/signed_masks.py') or a.endswith(b'/quota.py') or a.endswith(b'/orientations.py') for a in args):live.append(str(p))
 except OSError:pass
assert not live,live
report={'entries':len(rs),'raw_hashes_valid':True,'http_receipts':len(receipts),'receipt_body_hashes_valid':True,'excluded':sum(x['outcome'].startswith('excluded') for x in rs.values()),'parked':sum(x['outcome'].startswith('parked') for x in rs.values()),'live_numerical_processes':live,'new_lean_endpoints':0,'credit':0}
(D/'outputs/final-audit.json').write_text(json.dumps(report,indent=2));print(report)
manifest={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(D.rglob('*')) if p.is_file() and p.name!='artifact-manifest.json' and not str(p.relative_to(D)).startswith('logs/audit')}
(D/'outputs/artifact-manifest.json').write_text(json.dumps(manifest,indent=2))
