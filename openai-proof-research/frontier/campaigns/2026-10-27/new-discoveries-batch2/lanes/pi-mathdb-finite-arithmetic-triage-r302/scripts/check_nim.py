import sys
def nim_period(S, N=4000):
    g=[0]*(N+1)
    for n in range(1,N+1):
        s=set()
        for m in S:
            if m<=n: s.add(g[n-m])
        i=0
        while i in s: i+=1
        g[n]=i
    # eventual period of g: find smallest p with tail period p
    def per(seq):
        n=len(seq)
        for p in range(1,n//2+1):
            if seq[n-p:]==seq[n-2*p:n-p]: return p
        return None
    tail=g[N-400:]
    pg=per(tail)
    V=[0 if x==0 else 1 for x in tail]
    pv=per(V)
    return pg,pv,g
bad=[]
S3=[]
for a in range(1,9):
    for b in range(a+1,14):
        for c in range(b+1,20):
            pg,pv,g=nim_period((a,b,c),N=2000)
            if pg!=pv: bad.append(((a,b,c),pg,pv))
for S in [(1,),(2,),(3,),(1,2),(1,3),(2,3),(1,4),(1,2,3),(2,3,4),(1,2,4),(1,3,4)]:
    pg,pv,g=nim_period(S,N=2000); print(S,pg,pv)
print("violations of 323014 period-equality among 3-element sets a<b<c<=19:",bad[:20], "count",len(bad))
# 375237: period in {a+b,b+c,c+a} for c != a+b
viol=[]
for a in range(1,9):
    for b in range(a+1,14):
        for c in range(b+1,20):
            if c==a+b: continue
            pg,_,_=nim_period((a,b,c),N=2000)
            if pg not in (a+b,b+c,c+a): viol.append(((a,b,c),pg))
print("violations of 375237 period set:",viol[:20],"count",len(viol))
