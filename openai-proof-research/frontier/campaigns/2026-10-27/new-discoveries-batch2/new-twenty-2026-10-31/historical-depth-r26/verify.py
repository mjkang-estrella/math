import pathlib,json,hashlib,resource,os
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(30,30));os.sched_setaffinity(0,{0,1})
D=pathlib.Path(__file__).resolve().parent;h=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'reservation.json').read_text());out=json.loads((D/'results.json').read_text());assert set(out)==set(map(str,r['ids'])) and len(out)==40
for p,sha in r['prior_report_hashes'].items():assert h(pathlib.Path(p).read_bytes())==sha
chunks={}
for id,x in out.items():
 b=x['raw'];p=pathlib.Path(b['path']);chunks.setdefault(str(p),p.read_bytes());data=chunks[str(p)];assert h(data)==b['chunk_sha256'];line=data.splitlines(keepends=True)[b['line_1based']-1];assert line==(D/'raw'/f'{id}.jsonl').read_bytes();assert h(line)==b['raw_line_sha256'];assert json.loads(line)['statement']==x['literal_statement'];assert h(x['literal_statement'].encode())==x['literal_statement_sha256'];assert x['accepted_credit']==0 and not x['Lean_endpoint']
for p in (D/'sources').glob('*.receipt.json'):
 x=json.loads(p.read_text())
 if 'sha256' in x:assert h((p.parent/p.name.replace('.receipt.json','')).read_bytes())==x['sha256']
assert sum(x['new_primary_body_review'] for x in out.values())==3
print('PASS: 40 exact assigned IDs, old reports, raw lines/full chunks, statement hashes, retained source bodies; zero credit, 3 new primary/proof depth updates.')
print('Integrity verification is not mathematical or novelty acceptance.')
