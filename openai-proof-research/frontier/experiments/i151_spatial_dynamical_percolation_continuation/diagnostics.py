"""New finite algebra checks; no percolation, PDE, or contribution certification."""
from fractions import Fraction as F
from itertools import combinations

def subsets(mask):
 s=mask
 while True:
  yield s
  if not s:break
  s=(s-1)&mask

def run():
 counts={'toggle_expansion':0,'cutoff_difference':0,'history_pivotal_extraction':0,'post_jump_pairing':0,'refresh_calibration':0}
 for n in range(1,4):
  states=1<<n
  for table in range(1<<states):
   f=[(table>>x)&1 for x in range(states)]
   for base in range(states):
    coef={s:sum((-1)**((s.bit_count()-u.bit_count()))*f[base^u] for u in subsets(s)) for s in range(states)}
    for active in range(states):
     assert sum(coef[s] for s in subsets(active))==f[base^active]
     counts['toggle_expansion']+=1
     # A fixed initial-important set need not be independent of base or f.
     retained=sum((1<<i) for i in range(n) if f[base]!=f[base^(1<<i)])
     assert sum(coef[s] for s in subsets(active) if s&~retained)==f[base^active]-f[base^(active&retained)]
     counts['cutoff_difference']+=1
    for selected in range(1,states):
     # At label i only site i can differ from label 0. Expand product (L_i-P0).
     ids=[i for i in range(n) if selected>>i&1]
     signed=0
     for branch in subsets(selected):
      value=1
      for i in ids:value*=int(f[base^((1<<i) if branch>>i&1 else 0)]!=f[base])
      signed+=(-1)**(len(ids)-branch.bit_count())*value
     want=1
     for i in ids:want*=int(f[base^(1<<i)]!=f[base])
     assert signed==want
     counts['history_pivotal_extraction']+=1
   influences=[[int(f[x]!=f[x^(1<<i)]) for i in range(n)] for x in range(states)]
   lam=[F(sum(z),2) for z in influences]
   g=lam[:]
   for power in range(4):
    left=sum(F(influences[x][i],2)*g[x^(1<<i)] for x in range(states) for i in range(n))/states
    right=sum(lam[x]*g[x] for x in range(states))/states
    assert left==right
    counts['post_jump_pairing']+=1
    # A lazy uniformized reversible semigroup step, retaining repeated sites.
    g=[(g[x]+sum(g[x^(1<<i)] for i in range(n)))/(n+1) for x in range(states)]
 for initial in (0,1):
  assert F(1,2)*F(1,2)==F(1,4)
  counts['refresh_calibration']+=1
 assert F(4,1)/F(4,9)==9
 assert F(3,2)**3*72<7**3
 return {'status':'PASS','arithmetic':'exact integers and fractions.Fraction','checks':counts,'scope':'finite Boolean toggle, centered-history and reversible post-jump identities; constants arithmetic only, not universal mathematics or semantic reading'}
