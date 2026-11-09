from pathlib import Path
import json,hashlib
D=Path.cwd();r=json.load(open('results.json'));ids=json.load(open('reservation.json'))['ids'];sha=lambda b:hashlib.sha256(b).hexdigest()
assert set(r)==set(map(str,ids)) and len(r)==20
chunks={}
for i,o in r.items():
 p=o['provenance'];raw=Path('raw/'+i+'.jsonl').read_bytes();assert raw.endswith(b'\n')
 assert sha(raw)==p['raw_sha256']
 assert sha(o['statement'].encode())==p['statement_utf8_sha256']
 path=p['chunk']
 if path not in chunks:
  b=Path(path).read_bytes();assert sha(b)==p['chunk_sha256'];chunks[path]=b.splitlines(keepends=True)
 assert chunks[path][p['line_1based']-1]==raw
 assert o['accepted_credit']==0 and not o['Lean_complete']
 for rec in o['source_receipts']:
  assert rec['status']==200 and sha(Path(rec['path']).read_bytes())==rec['sha256']
assert Path('SUMMARY.md').exists()
x={'exactly_20_keys':True,'all_raw_newlines_locations_and_hashes_verified':True,'source_body_receipt_hashes_verified':True,'all_credit_zero':True,'no_Lean_endpoint_claimed':True,'limitations':'No independent source fidelity, mathematical or novelty review performed. Full requested deep pass remains incomplete.'}
Path('outputs/validation.json').write_text(json.dumps(x,indent=2)+'\n');print(x)
