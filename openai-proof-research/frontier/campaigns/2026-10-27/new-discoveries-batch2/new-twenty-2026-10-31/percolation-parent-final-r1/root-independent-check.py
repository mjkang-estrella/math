def vec(i):
    if i<25: return (1,i//5,i%5)
    if i<30: return (0,1,i-25)
    return (0,0,1)
V=[vec(i) for i in range(31)]
inc=[[sum(a*b for a,b in zip(V[l],V[p]))%5==0 for p in range(31)] for l in range(31)]
assert all(sum(row)==6 for row in inc)
lines=[[p for p in range(31) if inc[l][p]] for l in range(31)]
def step(S,r):
    T=set(S)
    for L in lines:
        if sum(p in S for p in L)>=r: T.update(L)
    return frozenset(T)
def closure(S,r):
    S=frozenset(S); t=0
    while True:
        T=step(S,r)
        if T==S: return S,t
        S=T; t+=1
def info(mask,r):
    A=frozenset(i for i in range(31) if mask>>i&1)
    C,t=closure(A,r)
    full=len(C)==31
    minimal=full and all(len(closure(A-{v},r)[0])<31 for v in A)
    return len(A),full,t,minimal
for mask,r in [(70588740,4),(241579737,5)]:
    print(mask,r,'size,percolates,time,minimal =',info(mask,r))
