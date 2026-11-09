# Exhaustive search: integer weights w_1>=...>=w_m>=1, all quotas 1<=q<=N; check beta_i <= 2w/N
# for absolute (gamma_i/2^(m-1)) and normalized (gamma_i/sum gamma) indices. Exact rationals.
from fractions import Fraction as F
from itertools import combinations_with_replacement as cwr
import sys,json
def gam(ws,q):
    m=len(ws);g=[0]*m
    for mask in range(1<<m):
        t=sum(ws[i] for i in range(m) if mask>>i&1)
        if t<q: continue
        for i in range(m):
            if mask>>i&1 and t-ws[i]<q: g[i]+=1
    return g
maxm=int(sys.argv[1]);maxw=int(sys.argv[2])
first={'absolute':None,'normalized':None,'normalized_majority':None}
for m in range(1,maxm+1):
  for ws in cwr(range(maxw,0,-1),m):
    N=sum(ws);w=max(ws);b=F(2*w,N)
    for q in range(1,N+1):
        g=gam(ws,q);S=sum(g)
        for i in range(m):
            a=F(g[i],2**(m-1)); nn=F(g[i],S) if S else F(0)
            key=(m,N)
            if a>b and first['absolute'] is None: first['absolute']=dict(weights=ws,q=q,i=i,gamma=g,abs=str(a),bound=str(b))
            if nn>b and first['normalized'] is None: first['normalized']=dict(weights=ws,q=q,i=i,gamma=g,norm=str(nn),bound=str(b))
            if nn>b and 2*q>N and first['normalized_majority'] is None: first['normalized_majority']=dict(weights=ws,q=q,i=i,gamma=g,norm=str(nn),bound=str(b))
  print(m,json.dumps(first),flush=True)
# explicit family check (k;1^(k+1)), q=k+1
for k in range(1,12):
    ws=[k]+[1]*(k+1);N=2*k+1;q=k+1;g=gam(ws,q)
    print('family k=%d q=%d gamma_big=%d gamma_small=%d norm=%s abs=%s bound=%s viol_norm=%s viol_abs=%s'%(k,q,g[0],g[1],F(g[0],sum(g)),F(g[0],2**(len(ws)-1)),F(2*k,N),F(g[0],sum(g))>F(2*k,N),F(g[0],2**(len(ws)-1))>F(2*k,N)))
