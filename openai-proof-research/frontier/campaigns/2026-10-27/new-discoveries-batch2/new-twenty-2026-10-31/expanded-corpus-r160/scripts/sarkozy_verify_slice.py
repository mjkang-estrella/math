# Slice-level independent verifier: given slice X (coordinate vectors on positions 'used'), check that no difference of
# distinct elements equals the coefficient vector (restricted to 'used', zero elsewhere required) of b^k for any nonzero b with
# deg b <= (n-1)//k, computed by direct polynomial multiplication; also checks that every b^k vanishes off 'used'.
import sys,json,itertools
d=json.load(open(sys.argv[1])); p,k,n,used=d['p'],d['k'],d['n'],d['used']; X=[tuple(v) for v in d['slice']]
def mul(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): r[i+j]=(r[i+j]+x*y)%p
    return r
P=set(); e=(n-1)//k
for b in itertools.product(range(p),repeat=e+1):
    if not any(b): continue
    r=[1]
    for _ in range(k): r=mul(r,list(b))
    r=(r+[0]*n)[:n]
    assert all(r[i]==0 for i in range(n) if i not in used)
    P.add(tuple(r[i] for i in used))
assert len(set(X))==len(X)
bad=sum(1 for x in X for y in X if x!=y and tuple((a-b)%p for a,b in zip(x,y)) in P)
full=len(X)*p**(n-len(used)); bound=p**(n*(1-1/k**2))
print('p',p,'k',k,'n',n,'slice',len(X),'|A|',full,'bound',bound,'violations',bad,'COUNTEREXAMPLE' if bad==0 and full>bound else '')
