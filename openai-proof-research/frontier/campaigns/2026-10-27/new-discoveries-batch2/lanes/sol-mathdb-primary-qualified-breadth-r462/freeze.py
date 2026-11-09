import json,hashlib,pathlib,datetime
L=pathlib.Path(__file__).resolve().parent; B=L.parent
names=['root-mathdb-breadth-intake-r461','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
refs=[]
def bind(p,role):
 refs.append(dict(path=str(p),bytes=p.stat().st_size,sha256=h(p),role=role))
for n in names:
 d=B/n;m=json.loads((d/'manifest.json').read_text());bind(d/'manifest.json','manifest')
 files=m if isinstance(m,list) else m['files']+m.get('frozen_inputs',[]);files=[dict(path=k,**v) for k,v in files.items()] if isinstance(files,dict) else files
 for e in files:
  p=d/e['path'];assert p.is_file(),str(p)
  assert e.get('size',e.get('bytes',p.stat().st_size))==p.stat().st_size,str(p)
  assert h(p)==e['sha256'],str(p)
  bind(p,'manifest-member-in-place')
 print(n,'manifest files verified',len(files),'schema',type(m).__name__)
# Freeze metadata references only; no copied corpus or recursive reference traversal.
for n in ['ledger.json','prior-campaign-context.json']:
 p=B.parent/n
 if p.exists():bind(p,'required-admin')
(L/'bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
(L/'freeze-receipt.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',bound_files=len(refs),bindings_sha256=h(L/'bindings.json'),scope='Listed manifests verified against actual direct member originals. No upstream verifier executed.'),indent=2)+'\n')
for n in names:
 d=B/n
 for fn in ['reserved-ids.json','queue.json','coverage-delta.json','accepted-exclusions.json','historical-dispositions.json','bindings.json']:
  p=d/fn
  if p.exists():
   x=json.loads(p.read_text());print(n,fn,'type',type(x).__name__,'keys',list(x)[:18] if isinstance(x,dict) else 'length '+str(len(x)))
