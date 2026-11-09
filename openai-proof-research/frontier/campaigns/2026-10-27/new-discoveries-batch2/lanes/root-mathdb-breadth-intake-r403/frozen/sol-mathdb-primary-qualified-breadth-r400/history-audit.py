from pathlib import Path
import json,hashlib
O=Path(__file__).resolve().parent;L=O.parent;out=[]
for name in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363','root-mathdb-breadth-intake-r399']:
 for r in json.loads((L/name/'bindings.json').read_text()):
  p=Path(r['original']);b=p.read_bytes();out.append({'path':str(p),'expected_sha256':r['sha256'],'actual_sha256':hashlib.sha256(b).hexdigest(),'actual_size':len(b),'expected_size':r.get('size',r.get('bytes')),'sha_matches':hashlib.sha256(b).hexdigest()==r['sha256'],'size_matches_if_present':r.get('size',r.get('bytes',len(b)))==len(b)})
(O/'historical-binding-audit.json').write_text(json.dumps(out,indent=2)+'\n');print('hash mismatches',sum(not r['sha_matches'] for r in out),'absent sizes',sum(r['expected_size'] is None for r in out))
