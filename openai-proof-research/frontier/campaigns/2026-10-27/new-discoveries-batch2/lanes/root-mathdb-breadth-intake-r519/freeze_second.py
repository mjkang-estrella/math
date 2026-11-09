import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;rows=json.loads((P/'bindings.json').read_text())
for src in sorted((L/'sol-mathdb-primary-qualified-breadth-r518').rglob('*')):
 if not src.is_file():continue
 dst=P/'frozen'/src.relative_to(L);dst.parent.mkdir(parents=True,exist_ok=True);b=src.read_bytes();dst.write_bytes(b)
 rows.append({'original':str(src),'copy':str(dst),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'bindings.json').write_text(json.dumps(rows,indent=2)+'\n');print('frozen total',len(rows))
