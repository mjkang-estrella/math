from pathlib import Path
import hashlib,json,datetime
D=Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert len(r)==40 and set(map(int,r))==set(ids)
chunks={};n=0
for k,o in r.items():
 p=o['provenance'];chunk=Path(p['chunk'])
 if chunk not in chunks:
  data=chunk.read_bytes();assert sha(data)==p['chunk_sha256'];chunks[chunk]=data.splitlines(keepends=True)
 raw=(D/f'raw/{k}.jsonl').read_bytes();assert raw==chunks[chunk][p['line_1based']-1] and raw.endswith(b'\n');assert sha(raw)==p['raw_sha256'];assert sha(o['statement'].encode())==p['statement_utf8_sha256'];assert not o['accepted'] and o['discovery_credit']==0 and o['lean_endpoint'] is None;n+=1
receipts=0
for p in (D/'sources').glob('*.receipt.json'):
 o=json.loads(p.read_text())
 if o.get('status')==200:
  b=Path(o['path']).read_bytes();assert sha(b)==o['sha256'] and len(b)==o['bytes'];receipts+=1
manifest={str(p.relative_to(D)):sha(p.read_bytes()) for p in D.rglob('*') if p.is_file() and '.venv' not in p.parts and '__pycache__' not in p.parts and p.name not in ['manifest.json','validation.json']}
(D/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'raw_lines_verified':n,'download_receipts_verified':receipts,'manifest_files':len(manifest),'campaign_count_unchanged':'12/20 beyond39','claim':'INCOMPLETE checkpoint, no Lean theorem or acceptance'};(D/'validation.json').write_text(json.dumps(report,indent=2)+'\n');print(report)
