from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
d=json.loads((L/'frozen/sol-median-dynamics-breadth-depth-r1/certificate-results.json').read_text())['integer_certificate']
s='import Mathlib.Tactic.NormNum\nset_option autoImplicit false\nset_option warningAsError true\nnamespace MedianTemporal.IntegerLeaf\n'
for key in ['A','B','C','D','W']:s+=f'def {key} : ℤ := {d[key]}\n'
s+='theorem lower_leaf : 1000000*(D*A-W*C) > 18*W*(D*B+C) := by\n  norm_num [A,B,C,D,W]\n'
s+='theorem upper_leaf : 1000000*(D*A+W*C) < 19*W*D*B := by\n  norm_num [A,B,C,D,W]\n'
s+='theorem positive_leaf : 0 < D*A-W*C := by\n  norm_num [A,B,C,D,W]\nend MedianTemporal.IntegerLeaf\n'
(L/'IntegerLeaf.lean').write_text(s)
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
mf=P/'lake-manifest.json'
pins=json.loads(mf.read_text());assert len(pins['packages'])==9
assert next(p for p in pins['packages'] if p['name']=='mathlib')['rev']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(lean)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
support=[]
for rel in ['Probability/Distributions/Poisson/Basic.lean','Probability/Distributions/Exponential.lean','Probability/Independence/Process/HasIndepIncrements.lean','Analysis/Calculus/Deriv/Slope.lean']:
 p=P/'.lake/packages/mathlib/Mathlib'/rel;t=L/'support'/rel;t.parent.mkdir(parents=True,exist_ok=True)
 h=sha(p);t.write_bytes(p.read_bytes());assert sha(p)==sha(t)==h
 support.append({'original':str(p),'copy':str(t.relative_to(L)),'sha256':h})
(L/'support-freeze.json').write_text(json.dumps(support,indent=2)+'\n')
(L/'pins.json').write_text(json.dumps({'lean_sha256':sha(lean),'manifest_original':str(mf),'manifest_sha256':sha(mf),'packages':pins['packages']},indent=2)+'\n')
(L/'administrative/lake-manifest.json').write_bytes(mf.read_bytes())
print('generated explicit arithmetic leaves and pinned nine-package manifest')
