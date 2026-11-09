import pathlib,hashlib,json
O=pathlib.Path(__file__).resolve().parent
def bind(p):
 b=p.read_bytes();return dict(path=str(p.resolve()),size=len(b),sha256=hashlib.sha256(b).hexdigest())
rows=json.loads((O/'intake-validation.json').read_text())['bindings']+json.loads((O/'source-actual-bindings.json').read_text())
unique={}
for r in rows:
 a=bind(pathlib.Path(r['path']))
 assert all(a[k]==r[k] for k in ('size','sha256')),r['path']
 unique[a['path']]=a
for p in [O.parents[5]/'AGENTS.md']:
 # Mandatory ancestor instruction already read first; now record its actual bytes.
 if p.is_file():unique[str(p.resolve())]=bind(p)
(O/'flat-actual-bindings.json').write_text(json.dumps(sorted(unique.values(),key=lambda r:r['path']),indent=2)+'\n')
ex={'manifest.json','final-receipt.json'}
files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and str(p.relative_to(O)) not in ex:
  a=bind(p);a['path']=str(p.relative_to(O));files.append(a)
(O/'manifest.json').write_text(json.dumps(dict(excluded_exact_paths=sorted(ex),files=files),indent=2)+'\n')
print('Sealed',len(files),'payloads;',len(unique),'flat external bindings')
