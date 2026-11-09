# Which F_4 (subset of S_4, F_3=S_3) are (k,4)-balanced with |F_4| in {22,23,24}? (MathDB 342411)
from itertools import permutations, combinations
def std(seq):
    s=sorted(seq); return tuple(s.index(v)+1 for v in seq)
def patterns(p,k): return {std(c) for c in combinations(p,k)}
S3=list(permutations((1,2,3))); S4=list(permutations((1,2,3,4)))
P3={p:patterns(p,3) for p in S4}; P2={p:patterns(p,2) for p in S4}
def balanced(F4):
    for k,P in ((2,P2),(3,P3)):
        cnt={}
        for q in (S3 if k==3 else [(1,2),(2,1)]): cnt[q]=sum(q in P[p] for p in F4)
        if len(set(cnt.values()))>1: return False
    return True
res={}
for r in (0,1,2):
    for miss in combinations(S4,r):
        F4=[p for p in S4 if p not in miss]
        if (1,2,3,4) in miss or (4,3,2,1) in miss: continue
        if balanced(F4): res.setdefault(24-r,[]).append(miss)
for k,v in res.items(): print(k,len(v),v[:12])
