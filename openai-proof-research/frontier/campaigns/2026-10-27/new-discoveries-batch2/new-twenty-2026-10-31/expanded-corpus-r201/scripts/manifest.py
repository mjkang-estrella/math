import pathlib,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
files={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in D.rglob('*') if p.is_file() and '__pycache__' not in str(p) and p.name!='artifact-manifest.json' and not p.name.startswith('manifest-final.')}
(D/'outputs/artifact-manifest.json').write_text(json.dumps({'excludes':'manifest itself, Python bytecode caches and manifest-final driver logs/receipt','sha256':files},indent=2)+'\n');print('hashed',len(files),'stable files')
