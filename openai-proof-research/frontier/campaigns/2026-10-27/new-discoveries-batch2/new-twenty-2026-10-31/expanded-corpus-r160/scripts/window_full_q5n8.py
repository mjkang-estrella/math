# Complete verification for q=5, n=8 middle-window set A = {c : (c2,c3,c4) in X, (c0,c6) in U, c1,c5,c7 free}.
# A is a coset-product, so A-A = (X-X) x U x F_5^3 on (window, pair, free) positions. Check none is a nonzero square.
import json,itertools
q=5; beta=2
X=[tuple(v) for v in json.load(open('work/sarkozy/q5n4.json'))['slice']]
D=set(tuple((a-b)%q for a,b in zip(x,y)) for x in X for y in X)
def sq(b):
    r=[0]*8
    for i,x in enumerate(b):
        for j,y in enumerate(b):
            if i+j<8: r[i+j]=(r[i+j]+x*y)%q
            elif x*y%q: return None
    return tuple(r)
SQ=set()
for b in itertools.product(range(q),repeat=8):
    if any(b):
        s=sq(b)
        if s is not None: SQ.add(s)
bad=0; tested=0
for w in D:
    for t in range(q):
        for f1,f5,f7 in itertools.product(range(q),repeat=3):
            d=(t,f1,w[0],w[1],w[2],f5,(beta*t)%q,f7)
            if not any(d): continue
            tested+=1
            if d in SQ: bad+=1
size=len(X)*q*q**3
print('q=5 n=8 |A|',size,'bound 5^6 =',5**6,'distinct nonzero differences tested',tested,'nonzero squares deg<8',len(SQ),'violations',bad)
