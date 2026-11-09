import pathlib,json,hashlib,collections
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert set(r)==set(map(str,ids))and len(r)==20
for i,o in r.items():
 raw=(D/f'raw/{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert sha(raw)==o['provenance']['raw_sha256'];rawobj=json.loads(raw);assert rawobj['statement']==o['statement'];assert sha(o['statement'].encode())==o['provenance']['statement_utf8_sha256'];assert o['formal_endpoint'] is None and o['self_accept'] is False
 for src in o['source_versions']:
  rr=json.loads((D/src['receipt']).read_text());assert rr['status']==200;assert rr['sha256']==src['sha256'];assert sha(pathlib.Path(rr['path']).read_bytes())==src['sha256']
receipts=[]
for p in sorted((D/'sources').glob('*.receipt.json')):
 o=json.loads(p.read_text())
 if o.get('status')==200:assert sha(pathlib.Path(o['path']).read_bytes())==o['sha256']
 receipts.append({'path':str(p.relative_to(D)),**o})
(D/'outputs/source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
manifest={str(p.relative_to(D)):sha(p.read_bytes())for p in sorted(D.rglob('*'))if p.is_file()and p.name!='manifest.json'and not p.name.startswith('validation')}
(D/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'id_count':len(r),'source_version_pdfs_verified':sum(len(o['source_versions'])for o in r.values()),'source_receipts':len(receipts),'outcomes':dict(collections.Counter(o['outcome']for o in r.values())),'accepted_credit':0,'lean_packet':False,'manifest_files':len(manifest)},indent=2))
