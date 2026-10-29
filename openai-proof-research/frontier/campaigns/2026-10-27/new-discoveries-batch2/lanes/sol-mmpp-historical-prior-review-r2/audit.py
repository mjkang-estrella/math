from pathlib import Path
from fractions import Fraction as F
import json,hashlib,re
b=Path(__file__).resolve().parent;l=b.parent
out={}
for name in ['omega-tree.txt','openai-tree.txt']:
 p=l/'root-edge-irregulator-final-freeze-r1'/name;x=p.read_bytes();s=x.decode();hits=[z for z in s.splitlines() if re.search(r'mmpp|markov.?modulat|coxprocess|cox.?palm|palm.?survival|arrivalprocess',z,re.I)]
 out[name]={'sha256':hashlib.sha256(x).hexdigest(),'entries':len(s.splitlines()),'targeted_path_hits':hits,'scope':'Path screen only; no semantic universal negative'}
for n in ['registry-inspection.json','delta-body-receipts.json','source-prior-evidence.json']:
 x=(l/'sol-mmpp-survival-preliminary-review-r1'/n).read_bytes();p=b/'context'/n;p.write_bytes(x)
 out[n]={'sha256':hashlib.sha256(x).hexdigest()}
d=json.loads((b/'sources/omega-compare.json').read_text());out['fresh_delta']={'base':d['base_commit']['sha'],'head':json.loads((b/'sources/omega-head.json').read_text())[0]['sha'],'commits':d['total_commits'],'files':[z['filename'] for z in d['files']]}
# Complete explicit analytic bridge uses h<7/10^12, t<5 and sqrt(5h)<6/10^6.
h=F(7,10**12);Fbound=5*h+F(10,3)*F(6,10**6)
err=F(1,2)*h+F(5,4)*Fbound
assert err<F(1,3888)
out['bridge_arithmetic']={'h_upper':str(h),'F_upper':str(Fbound),'gap_error_upper':str(err),'error_lt_1_over_3888':True,'limit_gap_lt_minus_1_over_1944':True,'N':10**12,'construct_large_matrix':False}
(b/'audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
