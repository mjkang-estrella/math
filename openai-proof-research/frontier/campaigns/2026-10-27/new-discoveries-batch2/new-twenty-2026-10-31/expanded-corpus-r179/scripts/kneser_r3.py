# Search for counterexamples to Daneshpajouh's weaker conjecture (arXiv:2203.03019) for r=3:
# chi(KG^3(F_almost-3-stable)) >= ceil(cd_3(F)/2).  F = {pairs at distance<=2} U A, A almost 3-stable (all gaps>=3).
# If A nonempty with no 3 pairwise disjoint members then chi(KG^3(A))=1, so a counterexample needs cd_3(F)>=3.
import sys, itertools, random, time
def colorable(n, edges, deleted, r=3):
    V=[v for v in range(1,n+1) if v not in deleted]; E=[e for e in edges if not (set(e)&deleted)]
    inc={v:[e for e in E if v in e] for v in V}; col={}
    def ok(v):
        for e in inc[v]:
            if all(u in col for u in e) and len({col[u] for u in e})==1: return False
        return True
    def bt(i):
        if i==len(V): return True
        v=V[i]
        for c in range(r):
            if i==0 and c>0: break
            col[v]=c
            if ok(v) and bt(i+1): return True
            del col[v]
        return False
    return bt(0)
def cd(n,edges,limit):
    for t in range(limit+1):
        for D in itertools.combinations(range(1,n+1),t):
            if colorable(n,edges,set(D)): return t
    return limit+1
def nu_ge3(A):
    for a,b,c in itertools.combinations(A,3):
        if not (set(a)&set(b)) and not (set(a)&set(c)) and not (set(b)&set(c)): return True
    return False
mode=sys.argv[1]
if mode=='example':
    n=8; close=[(i,j) for i in range(1,n+1) for j in range(i+1,min(n,i+2)+1)]
    A=[(1,4),(4,7),(1,7),(2,5),(5,8),(2,8)]
    print('nu>=3?',nu_ge3(A),'cd_3=',cd(n,close+A,4))
else:
    n=int(sys.argv[2]); seed=int(sys.argv[3]); secs=float(sys.argv[4]); rnd=random.Random(seed)
    close=[(i,j) for i in range(1,n+1) for j in range(i+1,min(n,i+2)+1)]
    stab=[S for k in (2,3) for S in itertools.combinations(range(1,n+1),k) if all(b-a>=3 for a,b in zip(S,S[1:]))]
    t0=time.time(); best=0; tries=0
    while time.time()-t0<secs:
        tries+=1; A=[]
        order=stab[:]; rnd.shuffle(order)
        for S in order:
            if not nu_ge3(A+[S]): A.append(S)   # maximal family with no 3 pairwise disjoint members
        c=cd(n,close+A,3)
        if c>best: best=c; print('n',n,'cd',c,'A',A,flush=True)
        if c>=3: print('COUNTEREXAMPLE'); break
    print('n',n,'tries',tries,'best cd',best,'time',round(time.time()-t0,1))
