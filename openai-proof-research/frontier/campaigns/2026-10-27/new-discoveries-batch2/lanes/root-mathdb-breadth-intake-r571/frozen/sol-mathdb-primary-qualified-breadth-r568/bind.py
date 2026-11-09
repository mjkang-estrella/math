import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r567'; R=L/'pi-mathdb-full-corpus-inventory-r301'
entries={}
def bind(p,sha=None,size=None):
 p=p.resolve(); b=p.read_bytes(); h=hashlib.sha256(b).hexdigest()
 assert sha is None or h==sha,(str(p),'hash'); assert size is None or len(b)==size,(str(p),'size')
 entries[str(p)]={'path':str(p),'sha256':h,'size':len(b)}
 return b
for n in ['manifest.json','verification-receipt.json']:bind(I/n)
m=json.loads((I/'manifest.json').read_bytes()); expected={e['path'] for e in m['files']}
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}==expected|set(m['excluded_exact_paths'])
for e in m['files']:bind(I/e['path'],e['sha256'],e.get('size',e.get('bytes')))
for e in json.loads((I/'bindings.json').read_bytes()):
 for k in ['original','copy']:bind(pathlib.Path(e[k]),e['sha256'],e['size'])
assert (R/'manifest.json').read_bytes()==(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_bytes()
rm=json.loads(bind(R/'manifest.json'))
print('inventory keys',list(rm))
for e in rm['files']:
 if e['path'].startswith('corpus/') or e['path'].startswith('frozen_inputs/'):
  bind(R/e['path'],e['sha256'],e.get('bytes',e.get('size')))
for e in rm['frozen_inputs']:bind(R/e['path'],e['sha256'],e['bytes'])
print('frozen_inputs',rm.get('frozen_inputs'))
for p in [D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json']:
 if p.exists():bind(p)
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 for p in L.glob('*/'+name):
  if 'r304' in str(p):bind(p)
for p in L.glob('*r363/*'):
 if p.is_file() and p.suffix in ['.md','.json']:bind(p)
bind(L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py')
(D/'flat-bindings.json').write_text(json.dumps(list(entries.values()),indent=2)+'\n')
(D/'binding-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':len(entries),'integrity':'PASS','upstream_verifier_executed':False},indent=2)+'\n')
print('bound',len(entries))
