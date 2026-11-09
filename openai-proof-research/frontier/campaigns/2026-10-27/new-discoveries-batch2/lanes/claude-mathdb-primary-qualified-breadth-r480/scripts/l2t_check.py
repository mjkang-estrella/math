# Bounded validation for MathDB 337963 proof brief (not a proof). Random + exhaustive small linear 2-trees built by
# t1={a,b,c}, e1={b,c}; step j adds w_j on e_{j-1}; e_j={w_j,kappa_j}, kappa_j in e_{j-1}.
# Checks: (1) each switch cut C_j={x w_{j-1}, h w_{j-1}, h w_j} separates u=a from v=w_m;
# (2) diam <= s+2; (3) exact R(u,v) >= ceil(s/2)/3 (exact rational Laplacian solve).
import sys,random,itertools,json
from fractions import Fraction as F
from collections import deque
def build(choices):
    # choices[j] in {0,1}: 0 keep old kappa (fan continues), 1 keep newer vertex w_{j-1}
    V=['a','b','c'];E={frozenset('ab'),frozenset('ac'),frozenset('bc')};e=('b','c');m=len(choices)+2
    tri=[('a','b','c')];kappa=[None,None];cuts=[];s=0
    prev_e=None
    for j in range(2,m+1):
        w='w%d'%j;V.append(w);E|={frozenset((w,e[0])),frozenset((w,e[1]))};tri.append((e[0],e[1],w))
        if j<m:
            c=choices[j-2]
            if j==2: k=e[c]
            else:
                old,new=kappa[-1],'w%d'%(j-1)
                k=new if c else old
            kappa.append(k)
            if j>=3 and k!=kappa[-2]:
                s+=1;h=kappa[-2];x=[y for y in prev_e if y!=h][0]
                cuts.append((j,[frozenset((x,'w%d'%(j-1))),frozenset((h,'w%d'%(j-1))),frozenset((h,w))]))
            prev_e=e; e=(w,k)
    return V,E,s,cuts,'w%d'%m,kappa
def comps_sep(V,E,u,v):
    adj={x:[] for x in V}
    for ed in E:
        p,q=tuple(ed);adj[p].append(q);adj[q].append(p)
    seen={u};dq=deque([u])
    while dq:
        x=dq.popleft()
        for y in adj[x]:
            if y not in seen: seen.add(y);dq.append(y)
    return v not in seen
def diam(V,E):
    adj={x:[] for x in V}
    for ed in E:
        p,q=tuple(ed);adj[p].append(q);adj[q].append(p)
    D=0
    for s0 in V:
        d={s0:0};dq=deque([s0])
        while dq:
            x=dq.popleft()
            for y in adj[x]:
                if y not in d: d[y]=d[x]+1;dq.append(y)
        D=max(D,max(d.values()))
    return D
def resist(V,E,u,v):
    idx={x:i for i,x in enumerate(V)};n=len(V)
    L=[[F(0)]*n for _ in range(n)]
    for ed in E:
        p,q=[idx[t] for t in ed];L[p][p]+=1;L[q][q]+=1;L[p][q]-=1;L[q][p]-=1
    g=idx[v];keep=[i for i in range(n) if i!=g];A=[[L[i][k] for k in keep] for i in keep];b=[F(1) if i==idx[u] else F(0) for i in keep]
    N=len(A)
    for c in range(N):
        p=next(r for r in range(c,N) if A[r][c]!=0);A[c],A[p]=A[p],A[c];b[c],b[p]=b[p],b[c]
        for r in range(N):
            if r!=c and A[r][c]!=0:
                f=A[r][c]/A[c][c];A[r]=[x-f*y for x,y in zip(A[r],A[c])];b[r]-=f*b[c]
    pot=b[keep.index(idx[u])]/A[keep.index(idx[u])][keep.index(idx[u])]
    return pot
mode=sys.argv[1];bad=[];cnt=0;mn=None
if mode=='exh':
    for m in range(3,int(sys.argv[2])+1):
        for ch in itertools.product((0,1),repeat=m-2):
            V,E,s,cuts,v,_=build(list(ch));cnt+=1
            for j,C in cuts:
                if not comps_sep(V,E-set(C),'a',v): bad.append(('cut',ch,j))
            if diam(V,E)>s+2: bad.append(('diam',ch))
            R=resist(V,E,'a',v)
            if R< F((s+1)//2,3): bad.append(('R',ch,str(R),s))
            r=(float(R),s,diam(V,E));mn=r if mn is None or r[0]-((s+1)//2)/3<mn[0]-((mn[1]+1)//2)/3 else mn
else:
    random.seed(int(sys.argv[3]))
    for t in range(int(sys.argv[2])):
        m=random.randint(10,34);p=random.random();ch=[1 if random.random()<p else 0 for _ in range(m-2)]
        V,E,s,cuts,v,_=build(ch);cnt+=1
        for j,C in cuts:
            if not comps_sep(V,E-set(C),'a',v): bad.append(('cut',j))
        D=diam(V,E)
        if D>s+2: bad.append(('diam',D,s))
        R=resist(V,E,'a',v)
        if R< F((s+1)//2,3): bad.append(('R',str(R),s))
        if t<6: print(json.dumps(dict(m=m,s=s,diam=D,R=float(R),lower=((s+1)//2)/3)))
print(json.dumps(dict(mode=mode,instances=cnt,failures=len(bad),first=bad[:3])))
