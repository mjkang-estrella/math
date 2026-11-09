from fractions import Fraction as F
import json,pathlib,math
P=pathlib.Path(__file__).parent
# One rational tangent to caustic a=5,b=3; foci (+/-4,0).
norm2=F(3,25)**2+F(4,15)**2
product=(1-F(12,25)**2)/norm2
assert product==9
out={'executed':'exact rational focal-distance product for tangent at (3,12/5) to x²/25+y²/9=1','normal_squared':str(norm2),'product':str(product),'expected_b_squared':9,'scope':'one algebra sanity check; universal identity proved symbolically in source-coverage.md; no new theorem credit','apn_uncovered_pair_examples':[(m,r) for m in [24,26,28] for r in range(1,m//2) if math.gcd(r,m)==1 and not r<m/8-1]}
(P/'bounded-calculation.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
I=P.parent/'root-mathdb-breadth-intake-r553'
for name in ['adjudications.json','hypothesis-queue.json']:print(name,(I/name).read_text())
ids=set(json.loads((I/'reserved-ids.json').read_text())['ids'])
for f in [P.parent/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',P.parent/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 s=f.read_text();print(f.name,'assigned exact numeric occurrences', [i for i in ids if str(i) in s])
