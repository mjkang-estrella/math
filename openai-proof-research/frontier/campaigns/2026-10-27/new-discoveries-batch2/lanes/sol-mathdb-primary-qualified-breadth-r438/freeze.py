from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent;L=R.parent;B=L.parent
bindings={};checks=[]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for x in iter(lambda:f.read(1048576),b''):h.update(x)
 return h.hexdigest()
def bind(p,h=None,s=None):
 p=Path(p);z=p.stat().st_size;t=sha(p)
 assert h is None or h==t,str(p)
 assert s is None or s==z,str(p)
 bindings[str(p)]={'path':str(p),'sha256':t,'size':z}
def put(n,d):(R/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
for name in ['root-mathdb-breadth-intake-r437','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 base=L/name;m=base/'manifest.json';bind(m);d=json.loads(m.read_text());entries=d['files'] if isinstance(d,dict) else d
 if isinstance(d,dict):entries=entries+d.get('frozen_inputs',[])
 for e in entries:bind(base/e['path'],e['sha256'],e.get('size',e.get('bytes')))
 actual={str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()};listed={e['path'] for e in entries};extra=actual-listed
 print(name,'files',len(entries),'extra',sorted(extra))
 assert not listed-actual
 allowed={'manifest.json','verification-receipt.json'}
 assert extra<=allowed,(name,extra)
 checks.append({'lane':name,'files_checked':len(entries),'exact_exclusions':sorted(extra)})
 if name=='root-mathdb-breadth-intake-r437':
  for e in json.loads((base/'bindings.json').read_text()):bind(e['original'],e['sha256'],e.get('size',e.get('bytes')))
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L/'root-mathdb-breadth-intake-r433/reserved-ids.json'] :bind(p)
put('bindings.json',list(bindings.values()));put('freeze-receipt.json',{'status':'PASS','manifests':checks,'flat_originals':len(bindings),'recursive_binding_expansion':False})
print('FROZEN',len(bindings))
