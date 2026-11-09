# Diagnostic: independence-polynomial DP on forests; star(v,r) = i_{r-1}(T - N[v]).
import itertools,sys
def build(t):
    k=len(t); adj=[[] for _ in range(k+sum(t))]; n=k
    for i in range(k-1): adj[i].append(i+1); adj[i+1].append(i)
    for i,c in enumerate(t):
        for _ in range(c): adj[i].append(n); adj[n].append(i); n+=1
    return adj
def padd(a,b):
    r=[0]*max(len(a),len(b))
    for i,x in enumerate(a): r[i]+=x
    for i,x in enumerate(b): r[i]+=x
    return r
def pmul(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): r[i+j]+=x*y
    return r
def forest_poly(adj,alive):
    seen=set(); tot=[1]
    for s in alive:
        if s in seen: continue
        # iterative DFS order
        order=[];par={s:None};st=[s];seen.add(s)
        while st:
            u=st.pop();order.append(u)
            for w in adj[u]:
                if w in alive and w not in seen: seen.add(w);par[w]=u;st.append(w)
        inc={};exc={}
        for u in reversed(order):
            a=[0,1];b=[1]
            for w in adj[u]:
                if w in alive and par.get(w)==u:
                    a=pmul(a,exc[w]); b=pmul(b,padd(inc[w],exc[w]))
            inc[u]=a;exc[u]=b
        tot=pmul(tot,padd(inc[s],exc[s]))
    return tot
def analyse(t):
    adj=build(t); n=len(adj); deg=[len(a) for a in adj]; D=max(deg)
    full=forest_poly(adj,set(range(n))); alpha=len(full)-1
    while full[alpha]==0: alpha-=1
    polys=[forest_poly(adj,set(range(n))-{v}-set(adj[v])) for v in range(n)]
    res=[]
    for r in range(1,alpha+1):
        c=[(p[r-1] if r-1<len(p) else 0) for p in polys]; M=max(c)
        cent=[v for v in range(n) if c[v]==M]
        if all(all(deg[u]<D for u in adj[z]) for z in cent): res.append(r)
    return n,alpha,res
N=int(sys.argv[1]); out=[]
def comps(k,budget):
    if k==0: yield (); return
    for c in range(budget+1):
        for rest in comps(k-1,budget-c): yield (c,)+rest
for k in range(1,N+1):
  for t in comps(k,N-k):
    n=k+sum(t)
    if (k>=2 and (t[0]==0 or t[-1]==0)) or (k==1 and t[0]==0) or t>t[::-1]: continue
    n,a,res=analyse(t)
    for r in res: out.append((n,t,r,a))
print('strong failures',len(out))
print('min n', min(out)[:4] if out else None)
print('min r', sorted(out,key=lambda x:(x[2],x[0]))[:5])
print('min r/alpha', sorted(out,key=lambda x:(x[2]/x[3],x[0]))[:8])
print('n<=11 list', [o for o in out if o[0]<=11])
