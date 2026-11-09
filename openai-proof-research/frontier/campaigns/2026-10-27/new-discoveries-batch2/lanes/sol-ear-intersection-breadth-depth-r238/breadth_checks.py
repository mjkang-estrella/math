from pathlib import Path
from itertools import combinations,permutations
from math import comb
from fractions import Fraction as F
import json,time
L=Path(__file__).resolve().parent;start=time.monotonic()
# All letters distinct. A two-letter clue is an undirected king-graph edge.
V=range(9);E=[(a,b) for a,b in combinations(V,2) if max(abs(a//3-b//3),abs(a%3-b%3))==1]
assert len(E)==20
neighbors=[sum(1<<b for b in V if a!=b and max(abs(a//3-b//3),abs(a%3-b%3))==1) for a in V]
diff=set();automorphisms=0
for p in permutations(V):
 d=sum(1<<i for i,(a,b) in enumerate(E) if not (neighbors[p[a]]>>p[b]&1))
 if d:diff.add(d)
 else:automorphisms+=1
minimal=[]
for d in sorted(diff,key=int.bit_count):
 if not any(x&d==x for x in minimal):minimal.append(d)
valid=[];tested=0;full=(1<<20)-1
for inds in combinations(range(20),11):
 s=sum(1<<i for i in inds);tested+=1
 if all(s&d for d in minimal):valid.append(s)
out={'boggle':dict(grid_edges=E,permutations=362880,automorphisms=automorphisms,difference_masks=len(diff),minimal_masks=minimal,eleven_subsets_tested=tested,valid_eleven_clues=valid,seconds=time.monotonic()-start)}
# Source's proved dyadic edge case, no new divisibility result.
def vp(n,p):
 k=0
 while n%p==0:k+=1;n//=p
 return k
out['known_tripathy_edge']=[dict(e=e,g=comb(2**(e+1),2**e),valuation=vp(comb(2**(e+1),2**e),2)) for e in range(1,7)]
assert all(r['valuation']==1 for r in out['known_tripathy_edge'])
# Literal positive walks from -3 to 3, permitted steps 2,4,6.
# Intermediate vertices -1,1 have denominator 9-1=8.
out['hill_P3_n3']={'V6':'1','V2*V4':'1/4','V2^3':'1/64'}
assert F(1,8)+F(1,8)==F(1,4)
# Count lattice points in t*Delta_(2,4); extract h* by (1-z)^4.
counts=[sum(sum(x)==2*t for x in __import__('itertools').product(range(t+1),repeat=4)) for t in range(4)]
h=[sum((-1)**j*comb(4,j)*counts[k-j] for j in range(k+1)) for k in range(4)]
assert h==[1,2,1,0];out['ehrhart_B22']=dict(lattice_counts=counts,hstar=h)
(L/'breadth-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='boggle'},indent=2));print({k:v for k,v in out['boggle'].items() if k not in ['minimal_masks','grid_edges','valid_eleven_clues']});print('valid11',len(valid))
