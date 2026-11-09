import pathlib,json,hashlib,itertools,importlib.util
P=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads((P/'results.json').read_text());reserved=json.loads((P/'reservation.json').read_text())['ids']
assert set(r)==set(map(str,reserved)) and len(r)==20
for k,row in r.items():
 b=(P/'inputs'/f'{k}.jsonl').read_bytes();assert b.endswith(b'\n')
 assert sha(b)==row['provenance']['raw_sha256'];d=json.loads(b)
 assert sha(d['statement'].encode())==row['provenance']['statement_sha256']
 assert d['statement']==row['literal_statement'] and row['lean_endpoint'] is None
for f in (P/'receipts').glob('http-*.json'):
 d=json.loads(f.read_text())
 if d.get('body'):assert sha((P/d['body']).read_bytes())==d['sha256']
spec=importlib.util.spec_from_file_location('circle_geometry',P/'scripts/circles.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
circles=json.loads((P/'inputs/circle-search.json').read_text());hard=json.loads((P/'inputs/circle-hard-coloring.json').read_text())
for row in circles:
 normals,adj=m.arrangement(row['n'],row['normals'])
 assert all(m.dot(a,m.cross(b,c)) for a,b,c in itertools.combinations(normals,3))
 colors=row['colors'] if row['status']=='3-colorable' else hard['colors']
 assert len(colors)==len(adj) and all(c in [0,1,2] for c in colors)
 assert all(colors[v]!=colors[u] for v in range(len(adj)) for u in adj[v])
p=json.loads((P/'inputs/paley-search.json').read_text())
assert len(p['parameters'])==2170 and all(not x['extensions'] for x in p['parameters'])
assert not list(P.rglob('__pycache__'))
print('PASS: 20 exact ID bindings; raw line/newline and statement hashes; all retained HTTP-body hashes; 24 simple exact-normal arrangements with proper 3-colorings; 2170 no-extension records. No Lean theorem certified.')
