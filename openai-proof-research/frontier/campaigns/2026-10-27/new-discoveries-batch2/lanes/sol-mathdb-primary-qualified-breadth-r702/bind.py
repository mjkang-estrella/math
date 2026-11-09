import json,hashlib,pathlib
D=pathlib.Path(__file__).resolve().parent; L=D.parent; I=L/'root-mathdb-breadth-intake-r701'; R=L/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def sig(p):
 b=p.read_bytes();return {'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
bindings={}
def bind(p,h=None,n=None):
 s=sig(p);assert h is None or s['sha256']==h,str(p);assert n is None or s['size']==n,str(p);bindings[str(p)]=s;return s
bind(I/'manifest.json');bind(I/'verification-receipt.json')
m=load(I/'manifest.json');expected={x['path'] for x in m['files']}|set(m['excluded_exact_paths']);assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}==expected
for e in m['files']:bind(I/e['path'],e['sha256'],e['size'])
for e in load(I/'bindings.json'):
 for k in ['original','copy']:bind(pathlib.Path(e[k]),e['sha256'],e['bytes'])
rm=load(R/'manifest.json');chunks=[e for e in rm['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
for e in chunks+rm['frozen_inputs']:bind(R/e['path'],e['sha256'],e['bytes'])
for rel in ['ledger.json','prior-campaign-context.json'] :bind(L.parent/rel)
for rel in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/DECISION.md']:bind(L/rel)
root=L.parents[4]
for rel in ['sources/upstream.json','sources/CONTENTS.md']:bind(root/rel)
(D/'flat-bindings.json').write_text(json.dumps(list(bindings.values()),indent=2)+'\n')
(D/'initial-checks.json').write_text(json.dumps({'all20chunks':True,'all8frozen':True,'intake_exact_payload':True,'direct_original_copy_pairs':len(load(I/'bindings.json')),'bindings':len(bindings)},indent=2)+'\n')
print('BOUND',len(bindings))
