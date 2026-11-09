import pathlib,json,hashlib,collections,re
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'results.json').read_text());reserved=json.loads((D/'reservation.json').read_text())['ids'];assert len(r)==20 and set(r)==set(map(str,reserved))
for i,o in r.items():
 raw=(D/f'raw/{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert sha(raw)==o['provenance']['raw_sha256'];assert sha(o['statement'].encode())==o['provenance']['statement_utf8_sha256'];assert json.loads(raw)['mathdb_id']==int(i)
for p in (D/'sources').glob('*.receipt.json'):
 o=json.loads(p.read_text());q=p.with_name(p.name.removesuffix('.receipt.json'))
 if 'sha256' in o:assert q.exists() and sha(q.read_bytes())==o['sha256'],p
reg=json.loads((D/'outputs/registry-screen.json').read_text());assert len(reg['github_queries'])==8
assert all(not o['truncated'] for o in reg['complete_scopes'].values())
assert not list((D/'lean').rglob('*.lean'))
assert (D/'SUMMARY.md').exists() and (D/'CANDIDATE.md').exists()
samples=[json.loads(l) for l in (D/'logs/splitting-random500.log').read_text().splitlines()];assert len(samples)==500
summary={'raw_records_validated':20,'github_repository_queries':8,'splitting_samples':len(samples),'splitting_coverable':sum(s['result'] is not None for s in samples),'splitting_cover_at_base':sum(bool(s['result'] and s['result']['cover_at_base']) for s in samples),'counterexamples':0,'qualified_candidates':0,'Lean_endpoints':0,'excluded':sum(o['outcome'].startswith('excluded') for o in r.values()),'parked':sum(o['outcome'].startswith('parked') for o in r.values()),'receipt_hashes':'all saved direct HTTP body hashes validated','review_limits':'not full literature clearance or all-version proof review'}
(D/'outputs/validation.json').write_text(json.dumps(summary,indent=2)+'\n')
files={str(p.relative_to(D)):sha(p.read_bytes()) for p in D.rglob('*') if p.is_file() and p.name not in ['manifest.json'] and '/tmp/' not in str(p) and '__pycache__' not in str(p)}
(D/'outputs/manifest.json').write_text(json.dumps(files,indent=2)+'\n');print(json.dumps(summary,indent=2))
