import pathlib,json,hashlib,math,collections
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert set(r)==set(map(str,ids)) and len(r)==20
for i,x in r.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==x['provenance']['raw_sha256'];assert hashlib.sha256(x['statement'].encode()).hexdigest()==x['provenance']['statement_utf8_sha256'];assert x['lean_endpoint'] is None and x['accepted_credit']==0
 for rc in x['source_receipts']:
  p=D/rc['receipt'];assert hashlib.sha256(p.read_bytes()).hexdigest()==rc['receipt_sha256']
for p in (D/'sources').glob('*.receipt.json'):
 j=json.loads(p.read_text())
 if j.get('sha256'):
  data=p.with_name(p.name[:-len('.receipt.json')]);assert hashlib.sha256(data.read_bytes()).hexdigest()==j['sha256'],p
assert not list(D.rglob('__pycache__'))
a=json.loads((D/'cyclic-exhaustive-prefix.json').read_text())['rows'][0];b=json.loads((D/'cyclic-prefix-part1.json').read_text())['rows'][0];c=json.loads((D/'cyclic-prefix-final.json').read_text())['rows'][0]
assert a['completed_negative_exact_cover_tests']+a['already_complete_residue_samples_skipped']==b['begin_index'];assert b['next_index']==c['begin_index'];assert c['next_index']==math.comb(135,3)==400995
assert sum(t['completed_negative_exact_cover_tests'] for t in [a,b,c])==399267;assert sum(t['already_complete_residue_samples_skipped'] for t in [a,b,c])==1728
for name in ['SUMMARY.md','CANDIDATE.md','RESEARCH.md','manifest.json','search-coverage.json']:assert (D/name).is_file()
print(json.dumps({'valid':True,'result_count':len(r),'outcomes':dict(collections.Counter(x['outcome'] for x in r.values())),'http_receipts':len(list((D/'sources').glob('*.receipt.json'))),'raw_provenance_verified':20,'cyclic_prefix_contiguity_verified':True,'bytecode_dirs':0,'lean_endpoints':0},indent=2))
