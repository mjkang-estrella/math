import pathlib,json,hashlib,shutil
P=pathlib.Path(__file__).resolve().parent
L=P.parent
rows=json.loads((P/'bindings.json').read_text())
assert isinstance(rows,list)
for name in ['sol-mathdb-linear-two-tree-prior-boundary-r502','sol-mathdb-primary-qualified-breadth-r500']:
 for src in sorted((L/name).rglob('*')):
  if not src.is_file(): continue
  dst=P/'frozen'/name/src.relative_to(L/name)
  dst.parent.mkdir(parents=True,exist_ok=True)
  data=src.read_bytes(); dst.write_bytes(data)
  rows.append(dict(original=str(src),copy=str(dst),sha256=hashlib.sha256(data).hexdigest(),size=len(data)))
(P/'bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Frozen bindings',len(rows))
