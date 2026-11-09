import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent;C=L/'pi-mathdb-full-corpus-inventory-r301'
H=lambda b:hashlib.sha256(b).hexdigest()
bindings=json.loads((P/'bindings.json').read_text())
m=json.loads((P/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_text())
e=next(x for x in m['files'] if x['path']=='tags/screening-tags.jsonl');src=C/e['path'];b=src.read_bytes()
assert len(b)==e.get('size',e.get('bytes')) and H(b)==e['sha256']
bindings.append({'original':str(src),'copy':str(src),'size':len(b),'sha256':H(b)})
src=L/'root-mathdb-breadth-intake-r515/verify.py';b=src.read_bytes();dst=P/'frozen/root-mathdb-breadth-intake-r515/verify.py';dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(b)
bindings.append({'original':str(src),'copy':str(dst),'size':len(b),'sha256':H(b)})
(P/'bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
print('routing metadata bound in place; predecessor helper frozen')
