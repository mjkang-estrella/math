import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1];exclude=['manifest.json','final-receipt.json'];rows=[]
assert 'expected_nonzero_exit=1' in (L/'packet/negative-check.log').read_text()
assert '"status": "PASS"' in (L/'packet/verify-preseal.log').read_text()
for p in sorted(L.rglob('*')):
 if p.is_file() and str(p.relative_to(L)) not in exclude:
  b=p.read_bytes();rows.append(dict(path=str(p.relative_to(L)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
(L/'manifest.json').write_text(json.dumps(dict(schema_version=1,generated_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),excluded_exact_relative_paths=exclude,files=rows),indent=2)+'\n')
print('Sealed',len(rows),'exact payload members; only exclusions',exclude)
