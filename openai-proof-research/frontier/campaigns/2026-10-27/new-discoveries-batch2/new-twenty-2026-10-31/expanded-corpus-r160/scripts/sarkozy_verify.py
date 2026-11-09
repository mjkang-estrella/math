# Independent verifier: A is a list of polynomials over F_p (coefficient tuples, index i = coeff of T^i, deg < n).
# Checks: all distinct, all deg < n, and for all u != v in A, u - v is not b^k for any nonzero b in F_p[T]
# (b ranges over ALL nonzero polys with deg b <= n-1, a superset of what can occur).
import sys,json,itertools
def mul(a,b,p):
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): r[i+j]=(r[i+j]+x*y)%p
    while len(r)>1 and r[-1]==0: r.pop()
    return tuple(r)
def norm(t):
    t=list(t)
    while len(t)>1 and t[-1]==0: t.pop()
    return tuple(t)
def main(path):
    d=json.load(open(path)); p=d['p']; k=d['k']; n=d['n']; A=[tuple(x) for x in d['A']]
    assert all(len(a)==n and all(0<=c<p for c in a) for a in A)
    assert len(set(A))==len(A)
    powers=set()
    for b in itertools.product(range(p),repeat=n):
        if not any(b): continue
        r=(1,)
        for _ in range(k): r=mul(r,norm(b),p)
        powers.add(r)
    bad=0
    for i in range(len(A)):
        for j in range(len(A)):
            if i==j: continue
            diff=norm(tuple((x-y)%p for x,y in zip(A[i],A[j])))
            if diff in powers: bad+=1
    bound=p**(n*(1-1/k**2))
    print('p',p,'k',k,'n',n,'|A|',len(A),'bound q^(n(1-1/k^2))',bound,'violations',bad,'COUNTEREXAMPLE' if bad==0 and len(A)>bound else '')
main(sys.argv[1])
