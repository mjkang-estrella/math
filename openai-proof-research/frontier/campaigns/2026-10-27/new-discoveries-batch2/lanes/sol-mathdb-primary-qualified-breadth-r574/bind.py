import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent; L=P.parent; B=L.parent; I=L/'root-mathdb-breadth-intake-r573'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def fp(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,e):
 a=fp(p);assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p);return a
out={}
def add(p):out[str(p)]=fp(p)
assert fp(I/'manifest.json')['sha256']=='322fe68829f8f42be94f48241a0d289e77e9d9aa900daf0d08ac3da4dbf75caf'
add(I/'manifest.json');add(I/'verification-receipt.json')
m=j(I/'manifest.json');actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()};assert actual=={e['path'] for e in m['files']}|set(m['excluded_exact_paths'])
for e in m['files']:out[str(I/e['path'])]=check(I/e['path'],e)
for e in j(I/'bindings.json'):
 for key in ['original','copy']:out[e[key]]=check(pathlib.Path(e[key]),e)
# Flat direct references, not recursive tree expansion.
for e in j(L/'sol-mathdb-primary-qualified-breadth-r570/flat-bindings.json'):
 out[e['path']]=check(pathlib.Path(e['path']),e)
cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:out[str(C/e['path'])]=check(C/e['path'],e)
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-decision-r363/DECISION.md']:
 if not p.exists():
  if 'r363' in str(p):p=list(L.glob('*r363/DECISION.md'))[0]
  else:raise AssertionError(p)
 add(p)
(P/'flat-bindings.json').write_text(json.dumps(list(out.values()),indent=2)+'\n')
(P/'intake-check.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'intake_payload_exact':True,'direct_original_copy_pairs':len(j(I/'bindings.json')),'original_corpus_chunks':20,'frozen_inputs':8,'bound_files':len(out),'upstream_verifier_executed':False},indent=2)+'\n')
print((P/'intake-check.json').read_text())
