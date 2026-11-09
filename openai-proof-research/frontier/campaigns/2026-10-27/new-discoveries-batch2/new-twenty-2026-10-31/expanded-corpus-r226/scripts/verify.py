from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parents[1]
H=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((L/'results.json').read_text());ids=set(map(str,json.loads((L/'reservation.json').read_text())['ids']));assert set(r)==ids and len(r)==20
verified=[]
for i,x in r.items():
 raw=(L/f'inputs/{i}.jsonl').read_bytes();p=x['provenance'];assert raw.endswith(b'\n');assert H(raw)==p['raw_sha256'];assert H(x['literal_statement'].encode())==p['statement_sha256']
 assert H(Path(p['chunk']).read_bytes())==p['chunk_sha256']
 with Path(p['chunk']).open('rb') as f:
  for n,b in enumerate(f,1):
   if n==p['line']:assert b==raw;break
 assert x['accepted_credit']==0 and x['lean_endpoint'] is None;verified.append(i)
http=0
for p in (L/'receipts').glob('2026*.json'):
 x=json.loads(p.read_text());assert H((L/'receipts'/x['body']).read_bytes())==x['sha256'];http+=1
for p in (L/'logs').glob('*.receipt.json'):
 x=json.loads(p.read_text());assert x['returncode']==0 and x['killed'] is None
assert not list(L.rglob('__pycache__'))
a=json.loads((L/'inputs/spanning-bits-1-150.json').read_text());b=json.loads((L/'inputs/spanning-1-40.json').read_text());assert len(a)==150 and len(b)==40
assert all(x['min_radius']==x['predicted'] for x in a+b)
assert all(x['min_radius']==a[x['k']-1]['min_radius'] for x in b)
(L/'inputs/final-validation.json').write_text(json.dumps(dict(ids=verified,http_bodies_checked=http,all_raw_line_and_chunk_hashes_valid=True,all_resource_runs_completed=True,no_bytecode=True,overlap_crosscheck=True),indent=2)+'\n')
print('PASS',len(verified),'records;',http,'HTTP bodies')
