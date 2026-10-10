"""Exact boundary/product/truncation and quantifier guards; stdlib only."""
import runpy,json
from pathlib import Path
from itertools import combinations
D=runpy.run_path('frontier/experiments/i29_common_base_entropy/diagnostics.py')
Q=D['Q']; mask=D['mask']; gibbs=D['gibbs']; ent=D['ent_iv']; geo=D['geometry']
A=[mask(t) for t in combinations(range(4),2) if len(set(t)&{0,1})==1]
B=[mask(t) for t in combinations(range(4),2) if len(set(t)&{0,3})==1]
C=sorted(set(A)&set(B)); assert C==[5,10]
# Add a common coloop 4 and loop 5, preserving labels 0,1 parallel only in M1.
AA=[a|16 for a in A];BB=[a|16 for a in B];CC=[a|16 for a in C]
p,x=gibbs(CC,6,[1,101,1,1,7,13]);p0,x0=gibbs(C,4,[1,101,1,1])
assert p==p0 and x==x0+[Q(1),Q(0)]
g=geo(AA,BB,CC,6)
# Direct product of two cycle pairs, independently tilted.
prod=[a|(b<<4) for a in C for b in C]
p2,x2=gibbs(prod,8,[1,2,1,1,1,5,1,1]);pL,xL=gibbs(C,4,[1,2,1,1]);pR,xR=gibbs(C,4,[1,5,1,1])
assert p2==[a*b for a in pL for b in pR] and x2==xL+xR
# Unequal ranks: truncations to k=2 of U(3,4), U(2,4) agree with size-2 common independents.
U3=[mask(t) for t in combinations(range(4),3)];U2=[mask(t) for t in combinations(range(4),2)]
assert not(set(U3)&set(U2));T3=[a for a in U2 if any(a&b==a for b in U3)];assert T3==U2
# H <= F is false, even for a single uniform matroid: log6 > log4.
a,b=D['log_iv'](Q(3,2));assert a>0
# Arbitrary laws at their means do not inherit max-entropy lower bounds.
# U(2,6), 3 disjoint atom law: F-H-(1/2)B = log3 - 2log(3/2)>0.
u,v=D['log_iv'](Q(3));lo,hi=D['log_iv'](Q(3,2));assert u-2*hi>0
out={'PASS':True,'loop_coloop_reduction':g,'one_matroid_parallel_labels':[0,1],
'product_probabilities':list(map(str,p2)),'unequal_rank_common_bases':0,'truncated_common_bases':U2,
'upper_F_failure_log_ratio_interval':[str(a),str(b)],
'arbitrary_law_failure_interval':[str(u-2*hi),str(v-2*lo)],
'explanation':'These are exact rational enumeration and interval tests; universal claims are proved in the report.'}
Path('frontier/experiments/i29_common_base_entropy/boundary-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
