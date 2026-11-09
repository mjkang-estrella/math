import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent;B=L.parent;I=L/'root-mathdb-breadth-intake-r723';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
refs={}
def bind(p,e=None):
 p=p.resolve();b=p.read_bytes();r={'path':str(p),'sha256':h(b),'size':len(b)}
 if e:assert r['sha256']==e['sha256'] and r['size']==e.get('size',e.get('bytes')),str(p)
 refs[str(p)]=r;return r
assert bind(I/'manifest.json')['sha256']=='31e61bcb13bcc169300bd6e8da4ed60363b921da9b2cfbb51fad364c23e9ae4b'
for n in ['verification-receipt.json']:bind(I/n)
m=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])=={e['path'] for e in m['files']}
for e in m['files']:bind(I/e['path'],e)
for e in j(I/'bindings.json'):
 for k in ['original','copy']:bind(pathlib.Path(e[k]),e)
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:bind(C/e['path'],e)
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'pi-mathdb-breadth-intake-r304/accepted-exclusions.json',L/'pi-mathdb-breadth-intake-r304/historical-dispositions.json']:
 if p.exists():bind(p)
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
(P/'initial-checks.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'intake_exact':True,'original_copy_pairs':len(j(I/'bindings.json')),'chunks':20,'frozen_inputs':8,'bound_count':len(refs)},indent=2)+'\n')
print(json.dumps(j(P/'initial-checks.json')))
print('frozen inputs',cm['frozen_inputs'])
print('record sample schema only')
with (C/chunks[0]['path']).open() as f:print(list(json.loads(next(f))))
