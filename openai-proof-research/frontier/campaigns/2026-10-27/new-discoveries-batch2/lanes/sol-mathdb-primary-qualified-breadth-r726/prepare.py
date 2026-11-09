import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent; L=P.parent; B=L.parent; I=L/'root-mathdb-breadth-intake-r725'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_text())
def binding(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,e):
 x=binding(p);assert x['size']==e.get('size',e.get('bytes')) and x['sha256']==e['sha256'],str(p)
def write(n,x):(P/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
refs=[I/'manifest.json',I/'verification-receipt.json']+[I/e['path'] for e in j(I/'manifest.json')['files']]
for e in j(I/'manifest.json')['files']:check(I/e['path'],e)
assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in j(I/'manifest.json')['files']}|{'manifest.json','verification-receipt.json'}
for e in j(I/'bindings.json'):
 for k in ['original','copy']:check(pathlib.Path(e[k]),e);refs.append(pathlib.Path(e[k]))
cm=j(C/'manifest.json'); chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
for e in chunks+cm['frozen_inputs']:check(C/e['path'],e);refs.append(C/e['path'])
refs += [B/'ledger.json', B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/upstream.json'),pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/CONTENTS.md')]
write('flat-bindings.json',[binding(p) for p in sorted(set(refs))])
write('pre-reading-checks.json',{'intake_exact_payload':True,'direct_original_copy_pairs':len(j(I/'bindings.json')),'original_chunks':20,'separate_frozen_inputs':8,'upstream_verifier_executed':False})
print('BOUND',len(set(refs)))
