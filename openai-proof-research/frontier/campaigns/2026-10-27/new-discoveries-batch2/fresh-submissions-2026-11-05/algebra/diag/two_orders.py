import itertools
from collections import Counter
def inv(s): return sum(1 for i in range(len(s)) for j in range(i+1,len(s)) if s[i]>s[j])
def maj(s): return sum(i+1 for i in range(len(s)-1) if s[i]>s[i+1])
def A(rho):
    n=len(rho);D=Counter()
    for s in itertools.permutations(range(n)):
        D[(inv(s),maj([rho[x] for x in s]))]+=1
    return D
def sym(D): return all(D[k]==D[(k[1],k[0])] for k in D)
for n in range(2,6):
    good=[r for r in itertools.permutations(range(n)) if sym(A(r))]
    print(n, len(good), 'of', len([1 for _ in itertools.permutations(range(n))]), good[:30] if n<=4 else good[:12])
