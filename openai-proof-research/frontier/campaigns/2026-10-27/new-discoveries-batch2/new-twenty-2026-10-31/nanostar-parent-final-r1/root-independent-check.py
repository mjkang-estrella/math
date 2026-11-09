import sys
def phi(n):
    r=n;m=n;p=2
    while p*p<=m:
        if m%p==0:
            while m%p==0: m//=p
            r-=r//p
        p+=1
    if m>1: r-=r//m
    return r
G=[3,167,334,19577,31657,39154,63314,702085,983055,1048576,1123336,1975461,2370559,2633948,3352289,3561823,4182461,4741118,5019445,5866457,8031112,8364922,11732914]
V=set()
for a in G:
    x=a
    while x not in V:
        V.add(x)
        if x==1: break
        x=phi(x)
adj={v:set() for v in V}
for v in V:
    if v!=1:
        w=phi(v); assert w in V; adj[v].add(w); adj[w].add(v)
E=sum(len(s) for s in adj.values())//2
def canon(u,par,g):
    return '('+''.join(sorted(canon(w,u,g) for w in g[u] if w!=par))+')'
# recursive model
def build():
    g={};cnt=[0]
    def new():
        cnt[0]+=1; g[cnt[0]]=set(); return cnt[0]
    def link(a,b): g[a].add(b); g[b].add(a)
    def arm(k):
        r=new()
        if k==0: return r
        u2=new(); link(r,u2); b=new(); link(u2,b)
        link(b,arm(k-1)); link(b,arm(k-1)); return r
    c=new()
    for _ in range(3): link(c,arm(3))
    return g,c
M,c=build()
# find centre of orbit tree: unique vertex whose canonical form equals model's centre form
cm=canon(c,None,M)
cents=[v for v in V if len(adj[v])==3 and canon(v,None,adj)==cm]
print('vertices',len(V),'edges',E,'model',len(M),'tree',E==len(V)-1,'iso_centres',cents)
