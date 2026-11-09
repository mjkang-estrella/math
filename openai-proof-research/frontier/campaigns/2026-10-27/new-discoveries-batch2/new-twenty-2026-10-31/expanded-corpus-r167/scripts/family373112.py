# Build free Laman bases B_n (even n>=8) from GCR`vo by pairs of Henneberg-2 splits with a common degree-3 vertex z
# (z nonadjacent to u,v), and verify by brute force: Laman, no tight X with 4<=|X|<=n-1, degree set {3,5}.
import sys,json,itertools
def ecount(E,X): return sum(1 for a,b in E if (X>>a)&1 and (X>>b)&1)
def check(n,E):
    if len(E)!=2*n-3: return 'edgecount'
    adj=[0]*n
    for a,b in E: adj[a]|=1<<b; adj[b]|=1<<a
    for X in range(1,1<<n):
        k=bin(X).count('1')
        if k<2: continue
        c=0; m=X
        while m:
            v=(m&-m).bit_length()-1; m&=m-1; c+=bin(adj[v]&X).count('1')
        c//=2
        if c>2*k-3: return 'not Laman'
        if c==2*k-3 and 4<=k<=n-1: return 'tight set size %d'%k
    return 'ok'
def h2(n,E,u,v,z):
    E=set(E); assert (min(u,v),max(u,v)) in E
    nb=lambda x:{b for a,b in E if a==x}|{a for a,b in E if b==x}
    assert z not in nb(u) and z not in nb(v) and z not in (u,v)
    E.remove((min(u,v),max(u,v))); w=n
    E|={(u,w),(v,w),(z,w)}
    return n+1,sorted(E)
def deg(n,E):
    d=[0]*n
    for a,b in E: d[a]+=1; d[b]+=1
    return d
n=8; E=sorted([(0,3),(0,5),(0,7),(1,4),(1,5),(1,7),(2,5),(2,6),(2,7),(3,6),(3,7),(4,6),(4,7)])
out=[]; NMAX=int(sys.argv[1])
while True:
    r=check(n,E); d=deg(n,E)
    out.append({'n':n,'check':r,'degree_multiset':sorted(d),'edges':E})
    print(n,r,sorted(set(d)),flush=True)
    if n+2>NMAX: break
    # choose z: a degree-3 vertex; edge uv with u,v not in N[z]
    for z in range(n):
        if d[z]!=3: continue
        nb={b for a,b in E if a==z}|{a for a,b in E if b==z}|{z}
        cand=[(a,b) for a,b in E if a not in nb and b not in nb]
        if len(cand)>=2: break
    (u,v)=cand[0]; out[-1].setdefault('moves',[]).append({'split':[u,v],'z':z,'new':n}); n,E=h2(n,E,u,v,z)
    nb={b for a,b in E if a==z}|{a for a,b in E if b==z}|{z}
    cand=[(a,b) for a,b in E if a not in nb and b not in nb]
    (u,v)=cand[0]; out[-1]['moves'].append({'split':[u,v],'z':z,'new':n}); n,E=h2(n,E,u,v,z)
json.dump(out,open(sys.argv[2],'w'),indent=0)
