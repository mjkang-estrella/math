import pathlib,json,hashlib
P=pathlib.Path(__file__).parent;L=P.parent
refs=json.loads((P/'flat-bindings.json').read_text())
for n in [578,642,684]:
 p=L/f'sol-mathdb-primary-qualified-breadth-r{n}'/('failures.md' if n==642 else 'failures.json');b=p.read_bytes();e=dict(path=str(p.resolve()),sha256=hashlib.sha256(b).hexdigest(),size=len(b));refs.append(e)
(P/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
for n in [578,642,684]:
 p=L/f'sol-mathdb-primary-qualified-breadth-r{n}'/('failures.md' if n==642 else 'failures.json');print(n,p.read_text())
ids={x['id'] for x in json.loads((P/'literal-records.json').read_text())}
C=L/'pi-mathdb-full-corpus-inventory-r301/frozen/root-mathdb-accepted-exclusions-r304';out={}
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 data=json.loads((C/n).read_text());matches=[]
 def walk(x):
  if isinstance(x,dict):
   if any(str(i) in json.dumps(x) for i in ids) and not any(isinstance(v,list) for v in x.values()):matches.append(x)
   for v in x.values():walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(data);out[n]=matches
(P/'exclusion-screen.json').write_text(json.dumps(out,indent=2)+'\n');print('r304 assigned matches',json.dumps(out))
