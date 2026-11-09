import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r565';C=L/'pi-mathdb-full-corpus-inventory-r301'
def h(b):return hashlib.sha256(b).hexdigest()
def j(p):return json.loads(p.read_text())
bindings={}
def bind(p,e=None):
 b=p.read_bytes();v={'path':str(p),'size':len(b),'sha256':h(b)}
 if e:assert v['size']==e.get('size',e.get('bytes')) and v['sha256']==e['sha256'],str(p)
 bindings[str(p)]=v;return b
bind(I/'manifest.json',{'size':10611,'sha256':'a7efa254ea8e6cbddbd51a32484eb7614ba41833b266288f1a9a2a7f3772e49e'})
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
for e in m['files']:bind(I/e['path'],e)
bind(I/'verification-receipt.json',{'size':446,'sha256':'ef11e1ce96b7c55e9160ed02cef5906a639a52458814771afa964e177f1dd815'})
for e in j(I/'bindings.json'):
 for k in ['original','copy']:bind(pathlib.Path(e[k]),e)
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:bind(C/e['path'],e)
# Direct flat references only, never recursive historical expansion.
for e in j(L/'sol-mathdb-primary-qualified-breadth-r562/flat-bindings.json'):bind(pathlib.Path(e['path']),e)
for n in ['ledger.json','prior-campaign-context.json']:bind(L.parent/n)
for p in sorted(L.glob('*r363*/**/*')):
 if p.is_file() and p.name in ['DECISION.md','SUMMARY.md','accepted-exclusions.json','historical-dispositions.json']:bind(p)
(P/'flat-bindings.json').write_text(json.dumps(list(bindings.values()),indent=2)+'\n')
print('Bound',len(bindings),'files; all20chunks+8inputs; intake exact; direct pairs PASS')
