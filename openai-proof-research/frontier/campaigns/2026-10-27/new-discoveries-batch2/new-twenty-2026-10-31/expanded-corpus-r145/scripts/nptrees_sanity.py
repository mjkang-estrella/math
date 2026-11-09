import sys,random,math,time
sys.path.insert(0,sys.argv[1])
import nptrees as T
rng=random.Random(1)
# 1) edge counts / connectivity / distinct canonical forms for n=9
def canon(adj):
    n=len(adj)
    def f(v,p): return '('+''.join(sorted(f(w,v) for w in adj[v] if w!=p))+')'
    return min(f(v,-1) for v in range(n))
forms=set()
for lay in T.trees(11):
    adj=T.adj_from_layout(lay); assert sum(map(len,adj))==2*10
    forms.add(canon(adj))
print('distinct n=11 trees',len(forms))
lay=next(T.trees(12)); adj=T.adj_from_layout(lay); f=T.search(adj,rng); print(lay,adj,f,T.bad_vertices(adj,f))
# 2) negative control: C_4 plus... K_{2,2}? gcd condition on graph where impossible: star? use the 4-cycle with labels 1..4:
c4=[[1,3],[0,2],[1,3],[0,2]]; print('C4',T.search(c4,rng,tries=20))
# known non-NP graph: cycle C_n with n = 2 mod 4 is not neighborhood-prime (Patel-Shrimali); test C_6, C_10
for n in (6,10,5,7,8):
    cyc=[[(i-1)%n,(i+1)%n] for i in range(n)]; print('C%d'%n, T.search(cyc,rng,tries=50) is not None)
t0=time.time(); c=sum(1 for _ in T.trees(19)); print('gen19',c,round(time.time()-t0,2))
