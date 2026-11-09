import sys,random,itertools
sys.path.insert(0,sys.argv[0].rsplit('/',1)[0])
from w2 import mis_list,cond2,pc
rnd=random.Random(1)
for trial in range(3000):
    n=rnd.randint(1,8); nb=[0]*n
    for i in range(n):
        for j in range(i+1,n):
            if rnd.random()<rnd.random(): nb[i]|=1<<j; nb[j]|=1<<i
    U=(1<<n)-1
    Ms=sorted(mis_list(n,nb,U))
    ind=[S for S in range(1<<n) if all(not(nb[v]&S) for v in range(n) if S>>v&1)]
    mx=sorted(S for S in ind if all((S|1<<v) not in set(ind) or S>>v&1 for v in range(n)))
    indset=set(ind)
    mx=sorted(S for S in ind if all(S>>v&1 or (S|(1<<v)) not in indset for v in range(n)))
    assert Ms==mx,(n,nb,Ms,mx)
    # brute cond2 literal: for every v and every maximal independent S of V\N[v], alpha(N(v)\N(S))==1
    def alpha(X): return max(pc(S) for S in ind if S&~X==0)
    lit=True
    for v in range(n):
        Y=U&~nb[v]&~(1<<v)
        indY=[S for S in ind if S&~Y==0]
        sY=set(indY)
        for S in indY:
            if all(S>>w&1 or not(Y>>w&1) or (S|(1<<w)) not in sY for w in range(n)):
                NS=0
                for w in range(n):
                    if S>>w&1: NS|=nb[w]
                if alpha(nb[v]&~NS)!=1: lit=False
    assert lit==cond2(n,nb,Ms),(n,nb)
print('selftest ok')
