import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'results.json').read_text());ids=set(map(str,json.loads((D/'reservation.json').read_text())['ids']));assert set(r)==ids and len(r)==20
for i,o in r.items():
 b=(D/'raw'/f'{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert sha(b)==o['provenance']['raw_sha256'];assert sha(o['statement'].encode())==o['provenance']['statement_utf8_sha256']
for p in (D/'sources').glob('*.receipt.json'):
 o=json.loads(p.read_text());f=p.with_name(p.name.removesuffix('.receipt.json'))
 if 'sha256' in o:assert sha(f.read_bytes())==o['sha256'],p
assert not list(D.rglob('__pycache__'))
for p in (D/'logs').glob('*.receipt.json'):
 o=json.loads(p.read_text());assert o['returncode']==0 and o['cap_reason'] is None,p
manifest={str(p.relative_to(D)):sha(p.read_bytes()) for p in sorted(D.rglob('*')) if p.is_file() and p.name!='artifact-sha256.json'}
(D/'artifact-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(reserved_entries=len(r),raw_hashes_verified=True,http_hashes_verified=True,numerical_runs=len(list((D/'logs').glob('*.receipt.json'))),no_bytecode=True,credit=0,lean_endpoint=None,manifest_files=len(manifest))))
