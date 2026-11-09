# Exact degree of noninvertibility of extended promotion (Defant-Kravitz; definition from arXiv:2208.08665 Sec 1.1)
# over all naturally labeled posets on [n] (covers every iso class), MathDB 355748 bound (n+2)(n+1)/6.
import sys, itertools, json, resource
from fractions import Fraction
from collections import Counter
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,)*2); resource.setrlimit(resource.RLIMIT_CPU,(int(sys.argv[2]),)*2)
n=int(sys.argv[1])
def natural_posets(n):
    # up[i] = set of j>i with i<_P j ; build by adding element k with downset an order ideal of current poset
    def rec(k, down):
        if k==n: yield down; return
        # choose downset of new element k: any order ideal of {0..k-1}
        for mask in range(1<<k):
            S=[i for i in range(k) if mask>>i&1]
            if all(all((mask>>j)&1 for j in down[i]) for i in S):
                yield from rec(k+1, down+[frozenset(S)])
    yield from rec(0,[])
def deg(down):
    up=[[j for j in range(n) if i in down[j]] for i in range(n)]
    cnt=Counter()
    for perm in itertools.permutations(range(1,n+1)):
        L=list(perm)  # L[x] label of element x
        inv=[0]*(n+1)
        for x,l in enumerate(L): inv[l]=x
        chain=[inv[1]]
        while up[chain[-1]]:
            chain.append(min(up[chain[-1]],key=lambda y:L[y]))
        M=[l-1 for l in L]
        for a,b in zip(chain,chain[1:]): M[a]=L[b]-1
        M[chain[-1]]=n
        cnt[tuple(M)]+=1
    import math
    return Fraction(sum(c*c for c in cnt.values()), math.factorial(n))
bound=Fraction((n+2)*(n+1),6); best=None; seen=0; viol=[]
for down in natural_posets(n):
    seen+=1; d=deg(down)
    if best is None or d>best[0]: best=(d,[sorted(s) for s in down])
    if d>bound: viol.append([str(d),[sorted(s) for s in down]])
print(json.dumps({'n':n,'naturally_labeled_posets':seen,'bound':str(bound),'max_deg':str(best[0]),'max_deg_float':float(best[0]),'argmax_downsets':best[1],'violations':viol[:5],'violation_count':len(viol)}))
