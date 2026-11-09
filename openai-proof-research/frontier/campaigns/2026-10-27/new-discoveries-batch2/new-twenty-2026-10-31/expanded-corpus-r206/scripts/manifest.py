import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
files={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in D.rglob('*') if p.is_file() and p.name!='manifest.json' and '/tmp/' not in str(p) and '__pycache__' not in str(p)}
(D/'outputs/manifest.json').write_text(json.dumps(files,indent=2)+'\n')
