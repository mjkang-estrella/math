from fractions import Fraction as Q
import json
from pathlib import Path
names=['A0','A1','B0','B1','C0','C1','D0','D1']
u=[(0,0,1),(0,0,1),(0,Q(2,3),Q(1,3)),(0,Q(2,3),Q(1,3)),(0,1,0),(1,0,0),(Q(2,3),Q(1,3),0),(1,0,0)]
assert all(sum(v)==1 and all(x>=0 for x in v) for v in u)
a=[[sum(min(x,y) for x,y in zip(v,w)) if i//2!=j//2 else Q(0) for j,w in enumerate(u)] for i,v in enumerate(u)]
d=list(map(sum,a));assert max(d)==Q(5,3)<2
out={'vertices':names,'matrix':[[str(x) for x in row] for row in a],'defects':list(map(str,d)),'maximum':str(max(d)),'predicted':2,'gap':str(2-max(d))}
Path(__file__).with_name('independent-arithmetic.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
