import itertools,math,json
from functools import lru_cache
from fractions import Fraction
from collections import Counter,defaultdict
from pathlib import Path
@lru_cache(None)
def parts(n,top=99):
    if n==0:return ((),)
    return tuple((i,)+p for i in range(min(n,top),0,-1) for p in parts(n-i,i))
def mul(A,B):
    C=defaultdict(int)
    for a,x in A.items():
        for b,y in B.items():C[tuple(sorted(a+b,reverse=True))]+=x*y
    return {p:x for p,x in C.items() if x}
P=[{():1}]
for n in range(1,10):
    C=defaultdict(int);C[(n,)]+=1
    for j in range(2,n+1):
        for p,x in P[n-j].items():C[tuple(sorted((j,)+p,reverse=True))]+=(j-1)*x
    P.append(dict(C))
@lru_cache(None)
def emonom(e,lam):
    if not e:return int(not any(lam))
    ans=0
    for s in itertools.combinations([i for i,x in enumerate(lam) if x],e[0]):
        nxt=list(lam)
        for i in s:nxt[i]-=1
        ans+=emonom(e[1:],tuple(nxt))
    return ans
def solve(M,b):
    A=[[Fraction(x) for x in row]+[Fraction(y)] for row,y in zip(M,b)];m=len(A)
    for i in range(m):
        r=next(j for j in range(i,m) if A[j][i]);A[i],A[r]=A[r],A[i]
        f=A[i][i];A[i]=[v/f for v in A[i]]
        for j in range(m):
            if j!=i and A[j][i]:
                f=A[j][i];A[j]=[x-f*y for x,y in zip(A[j],A[i])]
    return [r[-1] for r in A]
def proper(a,b,c):
    n=1+a+b+c;prev=[None];edges=[];v=1
    for leg in [a,b,c]:
        u=0
        for _ in range(leg):edges.append((u,v));u=v;v+=1
    back=[[u for u,v in edges if v==j] for j in range(n)]
    colors=[];cnt=Counter()
    def rec(used):
        j=len(colors)
        if j==n:
            lam=tuple(sorted(Counter(colors).values(),reverse=True));cnt[lam]+=1;return
        for x in range(used+1):
            if all(colors[u]!=x for u in back[j]):
                colors.append(x);rec(max(used,x+1));colors.pop()
    rec(0)
    return {p:x*math.prod(math.factorial(v) for v in Counter(p).values()) for p,x in cnt.items()}
tests=[]
for n in range(4,9):
    pp=parts(n);M=[[emonom(e,lam) for e in pp] for lam in pp]
    for a in range(1,n):
        for b in range(1,a+1):
            c=n-1-a-b
            if not 1<=c<=b:continue
            m=proper(a,b,c);sol=solve(M,[m.get(p,0) for p in pp]);got={p:int(v) for p,v in zip(pp,sol) if v}
            assert all(v.denominator==1 for v in sol)
            expect=Counter(P[n])
            for i in range(1,c+1):
                expect.update(mul(P[i],P[n-i]))
                for p,v in mul(P[b+i],P[a+c+1-i]).items():expect[p]-=v
            expect={p:v for p,v in expect.items() if v}
            assert got==expect,(a,b,c,got,expect)
            tests.append(dict(legs=[a,b,c],vertices=n,elementary={str(p):v for p,v in got.items()}))
@lru_cache(None)
def path_coefficient(t,u):
    if t<0 or u<0:return 0
    return 4*path_coefficient(t-1,u)+5*path_coefficient(t,u-1)+int((t,u) in [(0,0),(1,0),(0,1)])
A=path_coefficient(124,1);B=path_coefficient(5,0);C=path_coefficient(119,1)
assert A-B*C==-2499*4**122
out=dict(coefficient=A-B*C,path626=A,path25=B,path601=C,small_spiders=tests,test_count=len(tests),method='proper restricted-growth colorings; exact elementary-to-monomial matrix inversion; independent path recurrence')
Path('outputs/spider-review.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
