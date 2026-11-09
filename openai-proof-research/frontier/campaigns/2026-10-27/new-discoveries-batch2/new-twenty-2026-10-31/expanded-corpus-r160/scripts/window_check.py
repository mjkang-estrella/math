# Sanity check of Theorem 3 (middle-window construction). Builds A in P_{q,4m} from slice X (positions 2m-2r..2m+2r-2),
# pairs (c_i, c_{n-2-i}) in U={(t,beta t)} for even i<=2m-2r-2, odd outside positions free.
import sys,json,itertools,random
def build(q,m,r,X,beta):
    n=4*m; W=list(range(2*m-2*r,2*m+2*r-1)); pairs=[(i,n-2-i) for i in range(0,2*m-2*r-1,2)]
    odd_free=[i for i in range(1,n,2) if i not in W]
    A=[]
    for x in X:
        for tv in itertools.product(range(q),repeat=len(pairs)):
            for fv in itertools.product(range(q),repeat=len(odd_free)):
                c=[0]*n
                for i,v in zip(W,x): c[i]=v
                for (i,j),t in zip(pairs,tv): c[i]=t; c[j]=(beta*t)%q
                for i,v in zip(odd_free,fv): c[i]=v
                A.append(tuple(c))
    return A
def is_square(d,q):
    # brute: d (tuple, coefficients) is b^2 for some b?  deg b <= (deg d)//2 ; search over b with leading coeff square root
    deg=max((i for i,c in enumerate(d) if c),default=-1)
    if deg<0: return True
    if deg%2: return False
    h=deg//2
    for b in itertools.product(range(q),repeat=h+1):
        if b[h]==0: continue
        r=[0]*(2*h+1)
        for i in range(h+1):
            for j in range(h+1): r[i+j]=(r[i+j]+b[i]*b[j])%q
        if tuple(r)==tuple(d[:2*h+1]): return True
    return False
mode=sys.argv[1]
if mode=='full':  # q=3, m=2, r=1 with X = the plane slice found by exact search (9 points)
    q=3; X=[(0,0,0),(0,1,0),(0,2,0),(1,0,2),(1,1,2),(1,2,2),(2,0,1),(2,1,1),(2,2,1)]
    A=build(q,2,1,X,2); n=8
    bad=0
    for u in A:
        for v in A:
            if u!=v and is_square(tuple((a-b)%q for a,b in zip(u,v)),q): bad+=1
    print('q=3 n=8 r=1 |A|',len(A),'bound',3**6,'violations',bad)
else:
    q=5; X=[tuple(v) for v in json.load(open('work/sarkozy/q5n4.json'))['slice']]
    A=build(q,2,1,X,2); rnd=random.Random(5); bad=0; T=int(sys.argv[2])
    S=set(A); assert len(S)==len(A)
    for _ in range(T):
        u=rnd.choice(A); v=rnd.choice(A)
        if u!=v and is_square(tuple((a-b)%q for a,b in zip(u,v)),q): bad+=1
    # targeted: pairs differing only in window or only in one U-pair
    print('q=5 n=8 r=1 |A|',len(A),'bound',5**6,'random pairs',T,'violations',bad)
