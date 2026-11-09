from pathlib import Path
from itertools import permutations
from math import comb,prod
import json
D=Path(__file__).resolve().parents[1]
def b(n):return sum(2*comb(n+1,k-1)*comb(n+1,k)*comb(n+1,k+1) for k in range(1,n+1))//(n*(n+1)**2)
a=[[b(i+j+2) for j in range(6)] for i in range(6)]
v=sum((-1)**sum(p[i]>p[j] for i in range(6) for j in range(i+1,6))*prod(a[i][p[i]] for i in range(6)) for p in permutations(range(6)))
assert v==-115894592
assert v==next(int(r['determinant']) for r in json.loads((D/'outputs/baxter-hankel.json').read_text()) if r['shift']==1 and r['size']==6)
print(v)
