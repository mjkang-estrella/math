import pathlib,json,hashlib,datetime,re
D=pathlib.Path(__file__).resolve().parents[1];R=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert set(map(int,R))==set(ids) and len(R)==20
for i,r in R.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert hashlib.sha256(b).hexdigest()==r['provenance']['raw_sha256'];assert hashlib.sha256(json.loads(b)['statement'].encode()).hexdigest()==r['provenance']['statement_utf8_sha256'];assert r['credit']==0 and r['lean_endpoint'] is None
t=json.loads((D/'outputs/tableaux-results.json').read_text());assert [x['n'] for x in t]==list(range(1,31));assert all(not x['negative'] for x in t)
assert json.loads((D/'outputs/tableaux12-results.json').read_text())[-1]['n']==12
for m in [5,7,9]:
 for x in json.loads((D/f'outputs/fields-{m}.json').read_text()):
  assert x['ordinary_blocks']==x['expected']
  if 'extended_blocks' in x:assert x['extended_blocks']==x['extended_expected']
c=json.loads((D/'outputs/cycles-results.json').read_text());assert len(c)==265 and all(x['partition_2_4'] and x['partition_3_3'] for x in c)
assert sum(x['samples'] for x in json.loads((D/'outputs/rainbow-results.json').read_text()))==5500
for name in ['sphere-results.json','sphere-circles-results.json']:assert not json.loads((D/'outputs'/name).read_text())['violations']
reg=json.loads((D/'outputs/registry-screen.json').read_text());assert len(reg['queries'])<=8;assert all(x['total_count']==0 for x in reg['github_search_hits']);assert all(not x['truncated'] for x in reg['omega_path_screens'].values())
# Initial papers receipt file was overwritten by the second batch. Preserve honest
# reconstructed file provenance, never pretend mtime is an HTTP response timestamp.
receipts=[]
for p in sorted((D/'sources').glob('*')):
 if not re.fullmatch(r'\d{4}\.\d{4,5}\.(pdf|html)',p.name):continue
 a=p.stem;ext=p.suffix
 receipts.append({'url':('https://arxiv.org/pdf/' if ext=='.pdf' else 'https://arxiv.org/abs/')+a,'file':str(p.relative_to(D)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size,'file_write_utc':datetime.datetime.fromtimestamp(p.stat().st_mtime,datetime.timezone.utc).isoformat(),'receipt_type':'reconstructed local file provenance; successful fetch writes only, original first-batch HTTP receipt overwritten; filesystem time is not response header time'})
(D/'outputs/source-file-provenance.json').write_text(json.dumps(receipts,indent=2))
report={'results_entries':20,'candidates':0,'lean_invocations':0,'exact_gamma_max_n':30,'direct_permutation_orders':[11,12],'cycles_patterns':265,'rainbow_samples':5500,'sphere_violations':0,'field_count_mismatches':0,'registry_queries':len(reg['queries']),'source_receipt_limitation':'First papers batch HTTP receipts overwritten by second batch; recovered local file hashes, URL mapping and filesystem timestamps in source-file-provenance.json. No fabricated headers or original response timestamps.','resource_receipts':{p.name:json.loads(p.read_text()) for p in (D/'logs').glob('*.receipt.json')}}
(D/'outputs/validation.json').write_text(json.dumps(report,indent=2)+'\n')
# Exclude active report/validation receipts and logs from the stable artifact list.
manifest={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in D.rglob('*') if p.is_file() and p.name!='artifact-manifest.json' and not str(p.relative_to(D)).startswith(('logs/report','logs/validate'))}
(D/'outputs/artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('PASS: 20 dispositions, exact diagnostics consistent, no candidate or Lean claim.')
print('Omega relevant path hits:',json.dumps(reg['omega_path_screens']))
