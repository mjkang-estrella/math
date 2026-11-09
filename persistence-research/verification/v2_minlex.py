# Theorem C.2 check by a different algorithm: lexicographic linear-objective DP.
# For equal-length sorted digit strings, lex order == compare count vectors at the
# smallest digit where they differ (more copies => smaller). So the objective
# key = (len, -c2, -c3, -c4, -c6, -c8, -c9) is additive; DP over (a,b) is exact.
import sys
from math import prod
DIG=[(2,1,0),(3,0,1),(4,2,0),(6,1,1),(8,3,0),(9,0,2)]
IDX={2:1,3:2,4:3,6:4,8:5,9:6}
A,B=240,160
INF=None
best=[[None]*(B+1) for _ in range(A+1)]
best[0][0]=(0,0,0,0,0,0,0)
for a in range(A+1):
    for b in range(B+1):
        if a==b==0: continue
        cand=None
        for d,x,y in DIG:
            if a>=x and b>=y and best[a-x][b-y] is not None:
                k=list(best[a-x][b-y]); k[0]+=1; k[IDX[d]]-=1; k=tuple(k)
                if cand is None or k<cand: cand=k
        best[a][b]=cand
def closed(a,b):
    ra,rb=a%3,b%2; c={2:0,3:0,4:0,6:0,8:0,9:0}
    if rb==0:
        c[8]=(a-ra)//3; c[9]=b//2
        if ra==1: c[2]=1
        if ra==2: c[4]=1
    else:
        c[9]=(b-1)//2
        if ra==0: c[3]=1; c[8]=a//3
        if ra==1: c[6]=1; c[8]=(a-1)//3
        if ra==2: c[2]=1; c[6]=1; c[8]=(a-2)//3
    return c
bad=0; n=0
for a in range(A+1):
    for b in range(B+1):
        if a==b==0: continue
        n+=1
        k=best[a][b]; c=closed(a,b)
        kc=(sum(c.values()),-c[2],-c[3],-c[4],-c[6],-c[8],-c[9])
        assert prod(d**c[d] for d in c)==2**a*3**b
        if k!=kc: bad+=1; print("MISMATCH",a,b,k,kc) if bad<10 else None
print(f"pairs checked: {n}, mismatches vs closed form: {bad}")
c=closed(19,4); s=''.join(sorted('7'*6+''.join(str(d)*c[d] for d in c)))
print("reconstruct (19,4,6):", s, s=='277777788888899')

# Theorem C used constructively: a(k) = min over 7-smooth m with P(m)>=k-1 of minpre(m)
def Pi(n): return prod(int(ch) for ch in str(n))
def P(n):
    k=0
    while n>=10: n=Pi(n); k+=1
    return k
def minpre(m):
    e=[0,0,0,0]
    for i,p in enumerate((2,3,5,7)):
        while m%p==0: m//=p; e[i]+=1
    assert m==1
    c=closed(e[0],e[1]) if (e[0] or e[1]) else {}
    s=''.join(sorted('5'*e[2]+'7'*e[3]+''.join(str(d)*c[d] for d in c)))
    if len(s)==1: s='1'+s
    return int(s)
sm=[]
p2=1
while p2<10**30:
    p3=p2
    while p3<10**30:
        p5=p3
        while p5<10**30:
            p7=p5
            while p7<10**30: sm.append(p7); p7*=7
            p5*=5
        p3*=3
    p2*=2
Ps={m:P(m) for m in sm}
oeis=[10,25,39,77,679,6788,68889,2677889,26888999,3778888999,277777788888899]
got=[]
for k in range(3,12):
    got.append(min(minpre(m) for m in sm if m>=10 and Ps[m]>=k-1))
print("a(3..11) via Theorem C:", got, "matches OEIS A003001:", got==oeis[2:])
