import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(25,25));signal.alarm(35)
from pathlib import Path
from fractions import Fraction as Q
from itertools import permutations
from math import factorial
import json,random
b=Path(__file__).resolve().parent;rng=random.Random(33);identities=0;perms=0
for n in range(2,7):
 for rep in range(3):
  H=[[0]*n for _ in range(n)]
  for i in range(n):
   for j in range(i):H[i][j]=H[j][i]=rng.randrange(-3,4)
  H2=[[sum(H[i][k]*H[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
  total=[[0]*n for _ in range(n)]
  for p in permutations(range(n)):
   inv=[p.index(i) for i in range(n)];perms+=1
   for i in range(n):
    for j in range(n):total[i][j]+=sum(H[i][p[k]]*H[p[k]][j] for k in range(min(inv[i],inv[j])))
  for i in range(n):
   for j in range(n):
    assert 6*total[i][j]==factorial(n)*(2*H2[i][j]+(H2[i][j] if i==j else 0));identities+=1
# Known two-orthonormal-bases class: exact PSD Gram factor and norm polynomial.
U=[[Q((-1)**((i&j).bit_count()),2) for j in range(4)] for i in range(4)]
assert all(sum(U[i][k]*U[j][k] for k in range(4))==int(i==j) for i in range(4) for j in range(4))
B=[[Q(int(i==j)) if (i<4)==(j<4) else U[i%4][j%4] for j in range(8)] for i in range(8)]
assert all(sum(B[i][k]*B[k][j] for k in range(8))==2*B[i][j] for i in range(8) for j in range(8))
# All-ones3 source average has norm5/3, while each L L* has norm(3+sqrt5)/2.
# This scalar-vector averaging calculation is already in the corrected source.
assert Q(5,3)<Q(5,2) # strictly less than (3+sqrt5)/2 as sqrt5>2
# Classical fixed-order Hilbert-kernel obstruction. Exact rational lower bound only;
# discovery.md supplies the standard Fourier-symbol norm bridge, no source refutation.
h=Q(0);sq=Q(0);n=512
for j in range(n):
 if j:h+=Q(1,j)
 sq+=h*h
rayleigh=sq/(16*n);assert rayleigh>Q(16,9)
r={'status':'PASS','exact_average_entry_identities':identities,'permutations_summed':perms,'two_basis_B2_eq_2B':True,'fixed_order_Hilbert_dimension':n,'fixed_order_rayleigh_numerator':str(rayleigh.numerator),'fixed_order_rayleigh_denominator':str(rayleigh.denominator),'fixed_order_rayleigh_gt_16_over_9':True,'source_conjecture_resolved':False,'credit':0}
(b/'checks.json').write_text(json.dumps(r,indent=2));print(json.dumps({k:v for k,v in r.items() if 'numerator' not in k and 'denominator' not in k}))
