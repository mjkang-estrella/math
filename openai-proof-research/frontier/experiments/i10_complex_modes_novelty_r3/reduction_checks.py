"""Exact finite countermodels to proposed logical shortcuts, not prime experiments."""
from fractions import Fraction as F
from itertools import combinations
from evidence import write

# A PD-valued variable may be independent of this law: unsigned and parity
# observations then agree, while the order-four Fourier mode does not vanish.
law = [F(1,2), F(1,2), F(0), F(0)]
assert sum(law) == 1
assert sum((-1)**j*p for j,p in enumerate(law)) == 0
i_mode = (law[0]-law[2], law[1]-law[3])
assert i_mode == (F(1,2), F(1,2))

# Exact uniformity of a truncated residue alone permits a cofactor cancelling it.
m = 7
pairs = [(a, (-a)%m) for a in range(m)]
assert all((a+b)%m == 0 for a,b in pairs)
assert sorted(a for a,b in pairs) == list(range(m))

# Inclusion-exclusion must precede absolute values; this is the elementary
# algebra underlying, not a substitute for, the candidate's allocation reversal.
qs = [F(1,3), F(1,4), F(2,5)]
terms=[]
for r in range(len(qs)+1):
 for subset in combinations(qs,r):
  t=F((-1)**r)
  for q in subset: t*=q
  terms.append(t)
positive=F(1)
absolute=F(1)
for q in qs: positive*=1-q; absolute*=1+q
assert sum(terms)==positive
assert sum(map(abs,terms))==absolute

write('reduction-checks.json',{
 'purpose':'Exact logical countermodels; no asymptotic prime claim or proof certification.',
 'parity_balanced_mod4_law':[str(x) for x in law],
 'order_four_mode':[str(x) for x in i_mode],
 'truncated_uniform_total_constant':{'m':m,'total_residue':0,'pairs':pairs},
 'signed_recombination':{'signed_total':str(positive),'absolute_total':str(absolute)},
 'all_assertions_passed':True})
print('Exact shortcut and recombination checks passed.')
