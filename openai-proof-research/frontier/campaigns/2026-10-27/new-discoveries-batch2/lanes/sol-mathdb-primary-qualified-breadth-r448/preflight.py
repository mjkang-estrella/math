import json,hashlib,pathlib
R=pathlib.Path.cwd(); L=R/'frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes'; O=L/'sol-mathdb-primary-qualified-breadth-r448'
def load(p):return json.loads(p.read_text())
def h(p):
 d=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b)
 return d.hexdigest()
bound={};checks=[]
def bind(p):
 p=p.resolve();bound[str(p)]={'original':str(p),'sha256':h(p),'size':p.stat().st_size}
def check(p,e):
 bind(p); a=bound[str(p.resolve())];assert a['sha256']==e['sha256'],str(p)
 if 'size' in e or 'bytes' in e:assert a['size']==e.get('size',e.get('bytes')),str(p)
for lane in ['root-mathdb-breadth-intake-r447','pi-mathdb-full-corpus-inventory-r301','root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 d=L/lane;m=d/'manifest.json';bind(m);j=load(m)
 if isinstance(j,list): entries=j
 else:
  print(lane,'manifest keys',list(j));entries=j.get('files',[])+j.get('frozen_inputs',[])
 assert entries
 for e in entries:check(d/e['path'],e)
 actual={str(p.relative_to(d)) for p in d.rglob('*') if p.is_file()}
 declared={e['path'] for e in entries}
 assert actual==declared|{'manifest.json','verification-receipt.json'},(lane,sorted(actual-declared-{'manifest.json','verification-receipt.json'}), sorted(declared-actual))
 checks.append({'lane':lane,'entries':len(entries),'exact_set':True})
 if lane=='root-mathdb-breadth-intake-r447':
  for e in load(d/'bindings.json'):check(pathlib.Path(e['original']),e)
for p in [R/'AGENTS.md',R/'frontier/campaigns/2026-10-27/new-discoveries-batch2/AGENTS.md',R/'frontier/campaigns/2026-10-27/new-discoveries-batch2/ledger.json',R/'frontier/campaigns/2026-10-27/new-discoveries-batch2/prior-campaign-context.json',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:bind(p)
(O/'bindings.json').write_text(json.dumps(list(bound.values()),indent=2)+'\n');(O/'preflight.json').write_text(json.dumps(checks,indent=2)+'\n')
print('PASS',len(bound),'flat bindings',checks)
