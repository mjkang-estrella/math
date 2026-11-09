import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'reservation.json').read_text());x=json.loads((D/'results.json').read_text());assert set(x)==set(map(str,r['ids'])) and len(x)==20
for i,o in x.items():
 b=(D/'raw'/f'{i}.jsonl').read_bytes();assert b.endswith(b'\n') and sha(b)==o['provenance']['raw_sha256'];assert sha(o['statement'].encode())==o['provenance']['statement_utf8_sha256'];assert o['accepted_credit']==0
for p in (D/'sources').glob('*/receipt.json'):
 o=json.loads(p.read_text());assert o['status']==200;assert sha((p.parent/'body').read_bytes())==o['sha256']
assert not list(D.rglob('__pycache__'));assert all((D/p).exists() for p in ['SUMMARY.md','CANDIDATE.md','results.json']);assert json.loads((D/'logs/selfcheck-v2.receipt.json').read_text())['returncode']==0
manifest={str(p.relative_to(D)):sha(p.read_bytes()) for p in D.rglob('*') if p.is_file() and p.name not in ['artifact-manifest.json','validation.json']}
(D/'artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
summary={'reserved_entries':20,'excluded':sum(o['outcome'].startswith('EXCLUDE') for o in x.values()),'parked':sum(o['outcome'].startswith('PARK') for o in x.values()),'credit':0,'http_receipts':len(list((D/'sources').glob('*/receipt.json'))),'all_http_body_hashes_match':True,'raw_hashes_and_newlines_match':True,'bytecode_directories':0,'lean_invocations':0}
(D/'validation.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
