"""Finite exact C5 diagnostic; not a proof of the research calculation."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import json
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r164')
ALL=31; r=Q(5,2); M=2
stables=[0]+[(1<<i)|(1<<((i+2)%5)) for i in range(5)]
probs=[Q(1,2)]+[Q(1,10)]*5
assert all(sum(p for I,p in zip(stables,probs) if I>>v&1)==1/(2*r) for v in range(5))
def frac_ch(S):
 if S==ALL:return Q(5,2)
 if not S:return Q(0)
 return Q(2 if any((S>>i&1) and (S>>((i+1)%5)&1) for i in range(5)) else 1)
rows=[]
for E in [(31,31),(0b10101,0b01010),(0b11101,0b10111)]:
 for A in [0,0b00101,31]:
  for kind in ['fractional','count_one','count_union']:
   masses={};sums={}
   for seq in product(range(6),repeat=4):
    p=Q(1)
    for j in seq:p*=probs[j]
    W=[ALL,ALL]
    for j,c in enumerate(seq):W[j//2]&=~(stables[c]&E[j%2])
    val=frac_ch(W[0]&A) if kind=='fractional' else Q(((W[0] if kind=='count_one' else W[0]|W[1])&A).bit_count())
    for k in range(5):
     pref=seq[:k];masses[pref]=masses.get(pref,Q(0))+p;sums[pref]=sums.get(pref,Q(0))+p*val
   means={p:sums[p]/masses[p] for p in masses};maxvar=Q(0);maxstep=Q(0);contexts=0
   bound=Q(1,2) if kind=='fractional' else M*Q(A.bit_count())/(2*r)
   b=1 if kind=='fractional' else M
   for pref in means:
    if len(pref)==4:continue
    deltas=[means[pref+(c,)]-means[pref] for c in range(6)]
    var=sum(p*d*d for p,d in zip(probs,deltas))
    assert var<=bound,(E,A,kind,pref,var,bound)
    assert all(abs(d)<=b for d in deltas)
    maxvar=max(maxvar,var);maxstep=max(maxstep,*map(abs,deltas));contexts+=1
   rows.append({'eligibility':E,'A':A,'observable':kind,'conditional_contexts':contexts,'max_conditional_variance':str(maxvar),'bound_per_trial':str(bound),'max_abs_Doob_increment':str(maxstep),'increment_bound':b})
receipt={'graph':'C5','distribution':'empty with probability1/2; five independent pairs each1/10','r':'5/2','M':2,'copies':2,'trials_per_copy':2,'outcomes_each':6**4,'cases':len(rows),'conditional_contexts_total':sum(x['conditional_contexts'] for x in rows),'rows':rows,'scope':'Exact finite diagnostic only, no universal proof or correctness/contribution gate.'}
(R/'private/variance-diagnostic.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='rows'},indent=2))
