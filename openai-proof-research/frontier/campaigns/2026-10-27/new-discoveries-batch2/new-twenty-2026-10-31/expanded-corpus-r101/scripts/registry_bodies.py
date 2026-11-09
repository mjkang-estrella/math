from fetch import fetch,D
import json,hashlib,re
h=json.loads((D/'sources/trureturing-HEAD.json').read_text())['sha']
paths=['Problems/lichtenfelz-modin-preston-2026-zeitlin-sixj-identities.md','D5/S3/Quantum/Algebra/ZeitlinSixJ/Endpoint.lean','D5/S3/Quantum/Algebra/ZeitlinSixJ/Racah.lean']
for j,p in enumerate(paths):print(fetch(('omega-body-'+str(j)+'.txt',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{h}/{p}')))
p=D.parent/'fresh-corpus-r10/sources/registry-preprints.json';b=p.read_bytes();x=json.loads(b)
(D/'outputs/openai-cache-binding.json').write_text(json.dumps({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'head_unchanged':json.loads((D/'sources/math-HEAD.json').read_text())['sha'],'scope':'cached complete preprints listing only'},indent=2)+'\n')
print('openai path keywords',[(a.get('path')) for a in x.get('tree',[]) if re.search('Genocchi|Cambrian|Dixmier|Wigner|SignedEdge|Adverse|McDiarmid|Pixed|TreeCover|Gallai',a.get('path',''),re.I)])
