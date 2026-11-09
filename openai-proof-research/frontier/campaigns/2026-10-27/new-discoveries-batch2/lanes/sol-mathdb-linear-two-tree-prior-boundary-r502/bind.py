import pathlib,hashlib,json
O=pathlib.Path(__file__).resolve().parent
L=O.parent
I=L/'root-mathdb-linear-two-tree-review-intake-r501'
def bind(p):
 b=p.read_bytes();return dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
rows=[bind(I/'manifest.json'),bind(I/'bindings.json')]
m=json.loads((I/'manifest.json').read_text())
expected={r['path'] for r in m['files']}
actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
assert expected==actual,(expected^actual)
for r in m['files']:
 a=bind(I/r['path']);assert all(a[k]==r[k] for k in ('size','sha256')),r['path']
 rows.append(a)
pairs=json.loads((I/'bindings.json').read_text())
for r in pairs:
 for k in ('original','copy'):
  a=bind(pathlib.Path(r[k]));assert all(a[t]==r[t] for t in ('size','sha256')),r[k]
  rows.append(a)
(O/'intake-validation.json').write_text(json.dumps(dict(status='PASS',manifest_files=len(expected),direct_pairs=len(pairs),bindings=rows),indent=2)+'\n')
print('PASS',len(expected),len(pairs))
