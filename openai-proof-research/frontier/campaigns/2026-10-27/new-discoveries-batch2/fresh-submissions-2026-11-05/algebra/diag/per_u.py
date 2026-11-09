import itertools
from collections import Counter, defaultdict
def inv(s): return sum(1 for i in range(len(s)) for j in range(i+1,len(s)) if s[i]>s[j])
def maj(s): return sum(i+1 for i in range(len(s)-1) if s[i]>s[i+1])
def imaj(s):
    pos={v:i for i,v in enumerate(s)}; return sum(v+1 for v in range(len(s)-1) if pos[v+1]<pos[v])
def majlex(u,s): return sum(i+1 for i in range(len(s)-1) if (u[i],s[i])>(u[i+1],s[i+1]))
def std(w):
    r=sorted(w); return tuple(r.index(x) for x in w)
for m in [(2,1),(1,2),(2,2),(2,1,1),(3,2),(2,3)]:
    n=sum(m); base=[g for g,k in enumerate(m) for _ in range(k)]
    res=[]; resom=[]
    for u in sorted(set(itertools.permutations(base))):
        A=Counter(); Bc=Counter(); byom=defaultdict(lambda:[Counter(),Counter()])
        for s in itertools.permutations(range(n)):
            L=majlex(u,s)
            z=[s[i] for j in range(len(m)) for i in range(n) if u[i]==j]
            A[(inv(s),L)]+=1; Bc[(imaj(z),L)]+=1
            om=tuple(std([s[i] for i in range(n) if u[i]==j]) for j in range(len(m)))
            byom[om][0][inv(s)]+=1; byom[om][1][imaj(z)]+=1
        res.append(A==Bc); resom.append(all(a==b for a,b in byom.values()))
    print(m,'per-u equal:',all(res),res.count(False),'per-(u,omega) equal:',all(resom))
