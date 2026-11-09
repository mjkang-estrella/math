import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;L=P.parent
refs=json.loads((P/'flat-bindings.json').read_text())
for name in ['sol-mathdb-primary-qualified-breadth-r578','sol-mathdb-primary-qualified-breadth-r642','sol-mathdb-primary-qualified-breadth-r684']:
 p=L/name/'failures.json'
 if p.exists():
  b=p.read_bytes();refs.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
for e in refs:
 if any('/'+n+'/failures.json' in e['path'] for n in ['sol-mathdb-primary-qualified-breadth-r578','sol-mathdb-primary-qualified-breadth-r642','sol-mathdb-primary-qualified-breadth-r684']):print(e['path'],pathlib.Path(e['path']).read_text()[:6000])
