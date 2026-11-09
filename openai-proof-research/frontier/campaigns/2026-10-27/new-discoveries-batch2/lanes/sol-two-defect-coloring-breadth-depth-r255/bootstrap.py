import pathlib,hashlib,json,shutil,datetime
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
R=L.parent/'sol-spectral-energy-breadth-depth-r253'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
(L/'frozen').mkdir(exist_ok=True)
(L/'administrative').mkdir(exist_ok=True)
bindings=[]
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 p=B/name;q=L/'administrative'/name;shutil.copyfile(p,q)
for p in sorted(R.iterdir()):
 if p.is_file() and (p.suffix in ['.md','.json','.py','.txt']):
  q=L/'frozen'/p.name;a=sha(p);shutil.copyfile(p,q);assert a==sha(p)==sha(q)
  bindings.append(dict(original=str(p),copy=str(q),sha256=a))
# Bind immutable leaf sources without recursively copying history.
for folder in ['sources','frozen']:
 for p in sorted((R/folder).rglob('*')):
  if p.is_file():bindings.append(dict(original=str(p),sha256=sha(p),immutable_reference=True))
(L/'bindings.json').write_text(json.dumps(bindings,indent=2))
print(json.dumps({'bound':len(bindings),'utc':str(datetime.datetime.now(datetime.timezone.utc))}))
