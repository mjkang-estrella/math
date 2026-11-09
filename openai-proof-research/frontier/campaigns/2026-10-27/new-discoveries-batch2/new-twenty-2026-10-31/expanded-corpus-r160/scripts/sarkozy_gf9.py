# GF(9) = F_3[i]/(i^2+1); element a+b i encoded as 3*b+a. Slice graph for k=2,n=4: vertices F_9^3, connection set
# {(s^2, 2 s t, t^2)} u negatives over (s,t) != 0. Run ILS; then verify by recomputing squares of all b=b0+b1T+b2T^2+b3T^3.
import sys,os,itertools,json
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from ils import ils
def add(x,y): return 3*(((x//3)+(y//3))%3)+((x%3)+(y%3))%3
def neg(x): return 3*((-(x//3))%3)+((-(x%3))%3)
def mul(x,y):
    a,b=x%3,x//3; c,d=y%3,y//3
    return 3*((a*d+b*c)%3)+((a*c-b*d)%3)
F=range(9)
S=set()
for s in F:
    for t in F:
        if s or t:
            v=(mul(s,s),mul(2,mul(s,t)),mul(t,t)); S.add(v); S.add(tuple(neg(c) for c in v))
verts=list(itertools.product(F,repeat=3)); idx={v:i for i,v in enumerate(verts)}; N=len(verts)
adj=[0]*N
for i,v in enumerate(verts):
    for s in S: adj[i]|=1<<idx[tuple(add(a,b) for a,b in zip(v,s))]
print('N',N,'deg',len(S),'target slice >',81,flush=True)
best,it=ils(adj,N,float(sys.argv[1]),int(sys.argv[2]))
X=[verts[v] for v in sorted(best)]
# independent verification: all squares of polys of degree <=3 over GF(9) with degree(b^2)<4
def pmul(p,q):
    r=[0]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q): r[i+j]=add(r[i+j],mul(x,y))
    return r
P=set()
for b in itertools.product(F,repeat=4):
    if not any(b): continue
    r=pmul(list(b),list(b))
    while len(r)>1 and r[-1]==0: r.pop()
    if len(r)<=4:
        r=(r+[0]*4)[:4]
        if r[3]==0: P.add(tuple(r[:3]))
        else: P.add(('deg3',))
bad=sum(1 for x in X for y in X if x!=y and tuple(add(a,neg(b)) for a,b in zip(x,y)) in P)
print('q=9 slice best',len(X),'|A|',9*len(X),'bound 9^3=729','violations',bad,'COUNTEREXAMPLE' if bad==0 and 9*len(X)>729 else '')
json.dump({'q':9,'encoding':'a+b*i -> 3*b+a, i^2=-1','slice':X},open(sys.argv[3],'w'))
