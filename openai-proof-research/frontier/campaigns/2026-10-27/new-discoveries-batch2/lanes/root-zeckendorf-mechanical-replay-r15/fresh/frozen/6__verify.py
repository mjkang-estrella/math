import pathlib,json,hashlib
d=pathlib.Path(__file__).resolve().parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((d/'manifest.json').read_text())
assert set(m)=={str(p.relative_to(d)) for p in d.rglob('*') if p.is_file() and p.name not in ('manifest.json','verification-receipt.json')}
for name,digest in m.items(): assert h(d/name)==digest,name
rows=json.loads((d/'bindings.json').read_text())
for row in rows:
 assert h(pathlib.Path(row['original']))==row['sha256'],row['original']
 assert h(d/row['copy'])==row['sha256'],row['copy']
r=dict(status='PASS',files=len(m),bindings=len(rows),scope='integrity only; no new mathematical replay')
(d/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r))
