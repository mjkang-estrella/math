import pathlib,json,hashlib,collections
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();x=json.loads((D/'results.json').read_text());r=json.loads((D/'reservation.json').read_text())
assert set(map(int,x))==set(r['ids']) and len(x)==20
for k,v in x.items():
 b=(D/'raw'/f'{k}.jsonl').read_bytes();assert b.endswith(b'\n');assert sha(b)==v['provenance']['raw_sha256'];assert sha(v['statement'].encode())==v['provenance']['statement_utf8_sha256'];assert json.loads(b)['statement']==v['statement'];assert v['credit']==0
receipts=list((D/'sources').glob('*.receipt.json'))
for p in receipts:
 z=json.loads(p.read_text());body=p.with_name(p.name.removesuffix('.receipt.json'))
 if 'sha256' in z:assert sha(body.read_bytes())==z['sha256'],p
for row in json.loads((D/'polygon-coverage.json').read_text()):assert row['best_crossings']<=row['bound']
assert all(row['full_cover_through102_surviving_buckets']==0 for row in json.loads((D/'tree-refined-all.json').read_text()))
gao=json.loads((D/'gao-fast-coverage.json').read_text());assert gao[-1]['n']==9 and gao[-1]['count']==362880 and not any(z['negative'] for z in gao)
print(json.dumps({'ids':len(x),'http_receipts_hash_verified':len(receipts),'excluded':sum(v['outcome'].startswith('excluded') for v in x.values()),'parked':sum(v['outcome'].startswith('parked') for v in x.values()),'polygon_maxima':[[z['m'],z['n'],z['best_crossings'],z['bound']] for z in json.loads((D/'polygon-coverage.json').read_text())],'gao9':gao[-1]},indent=2))
files={str(p.relative_to(D)):sha(p.read_bytes()) for p in D.rglob('*') if p.is_file() and p.name!='manifest.json'}
(D/'manifest.json').write_text(json.dumps(files,indent=2)+'\n')
