import pathlib,json,hashlib,re
L=pathlib.Path.cwd();r=json.loads((L/'results.json').read_text());expected=json.loads((L/'reservation.json').read_text())['ids']
assert set(r)==set(map(str,expected)) and len(r)==20
for i,d in r.items():
 raw=(L/d['raw_file']).read_bytes(); assert raw.endswith(b'\n')
 assert hashlib.sha256(raw).hexdigest()==d['provenance']['raw_sha256']
 assert hashlib.sha256(d['literal_statement'].encode()).hexdigest()==d['statement_sha256']
 assert d['credit']==0 and not d['root_acceptance']
for p in ['012','021','102','120','201','210']:
 rows=[json.loads(x) for x in (L/f'logs/pattern12-{p}.log').read_text().splitlines()]
 assert rows[-1]['n']==12 and rows[-1]['avoid']==208012
 for d in rows:assert len({d['counts'][str(k)] for k in (4,8,16,32,64)})==1
for f in [L/'replay/formal/OrderedFull.lean',L/'replay/formal/Audit.lean']:
 assert not re.search(r'\b(sorry|admit|unsafe|native_decide|ofReduceBool)\b|^\s*axiom\b',f.read_text(),re.M)
 # isUnsafe appears only as a safe introspection property, not a forbidden keyword.
 assert f.read_bytes()==(L/'formal'/f.name).read_bytes()
for name in ['build','audit','checker']:
 e=(L/f'logs/replay-{name}.err').read_text();assert 'exit=0' in e,e
assert 'AUDITED 95 declarations' in (L/'logs/replay-audit.log').read_text()
manifest={str(f.relative_to(L)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(L.rglob('*')) if f.is_file() and f.name not in ['artifact-manifest.json'] and not str(f.relative_to(L)).startswith('logs/validate')}
json.dump(manifest,open(L/'outputs/artifact-manifest.json','w'),indent=2)
print('PASS: 20 entries, exact raw/statement hashes, six complete length-12 searches, strict fresh build/audit/checker, source identity, forbidden-token screen.')
