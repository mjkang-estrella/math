import itertools
from collections import Counter
def inv(s): return sum(1 for i in range(len(s)) for j in range(i+1,len(s)) if s[i]>s[j])
def majlex(u,s): return sum(i+1 for i in range(len(s)-1) if (u[i],s[i])>(u[i+1],s[i+1]))
def B(m):
    n=sum(m); base=[g for g,k in enumerate(m) for _ in range(k)]
    words=set(itertools.permutations(base)); D=Counter()
    for s in itertools.permutations(range(n)):
        for u in words: D[(inv(s),majlex(u,s))]+=1
    return D
def sym(D): return all(D[k]==D[(k[1],k[0])] for k in D)
for m in [(1,1),(2,1),(1,2),(1,1,1),(2,2),(3,1),(1,3),(2,1,1),(1,2,1),(1,1,2),(3,2),(2,3),(1,4),(2,2,1),(1,1,1,1),(1,1,1,1,1),(4,2),(3,3)]:
    print(m, sym(B(m)),flush=True)
