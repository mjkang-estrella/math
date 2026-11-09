import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
m={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in D.rglob('*') if p.is_file() and p.name!='manifest.json' and not str(p.relative_to(D)).startswith('logs/final-audit') and not str(p.relative_to(D)).startswith('logs/manifest')}
(D/'outputs/manifest.json').write_text(json.dumps(m,indent=2))
print(len(m),'stable files hashed; self-generating audit/manifest logs excluded')
