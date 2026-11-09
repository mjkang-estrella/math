# Separable-potential colourings for HJ(k,2) >= k:  blue iff phi(N) = sum_j g_j(N_j) == r (mod q), on count vectors N
# of [k]^(k-1).  Sufficient conditions (for every residue r):
#  (S) for every c with |c| = n-d, d>=1:  j -> g_j(c_j+d) - g_j(c_j) is a bijection [k] -> Z_q  (forces q = k)
#  (P) for every letter a<k-1 and t<=n:  s -> g_a(s) + g_{a+1}(t-s), s=0..t, is injective mod q.
import sys,json,time,random,itertools
sys.path.insert(0,__file__.rsplit('/',1)[0])
from hj_counts import comps
k=int(sys.argv[1]); lim=float(sys.argv[2]); seed=int(sys.argv[3]); q=k; n=k-1
rnd=random.Random(seed)
# constraints as tuples of variable pairs: star constraint for multiset of (c_j) values -> list over j of (j,c_j)
stars=set()
for d in range(1,n+1):
    for c in comps(n-d,k): stars.add((d,c))
stars=list(stars)
# variable index (j,s) s=1..n; g[j][0]=0
order=[(j,s) for s in range(1,n+1) for j in range(k)]
pos={v:i for i,v in enumerate(order)}
def need(v):  # position of variable v in order (or -1 for s=0)
    return -1 if v[1]==0 else pos[v]
starcons=[]
for d,c in stars:
    vars_=[((j,c[j]+d),(j,c[j])) for j in range(k)]
    last=max(max(need(a),need(b)) for a,b in vars_)
    starcons.append((last,vars_))
paircons=[]
for a in range(k-1):
    for t in range(1,n+1):
        terms=[((a,s),(a+1,t-s)) for s in range(t+1)]
        last=max(max(need(x),need(y)) for x,y in terms)
        paircons.append((last,terms))
bylast={}
for last,vs in starcons: bylast.setdefault(last,[]).append(('S',vs))
for last,vs in paircons: bylast.setdefault(last,[]).append(('P',vs))
g={(j,0):0 for j in range(k)}
t0=time.time(); nodes=[0]; res={}
def ok(i):
    for typ,vs in bylast.get(i,[]):
        if typ=='S':
            vals=[(g[a]-g[b])%q for a,b in vs]
        else:
            vals=[(g[x]+g[y])%q for x,y in vs]
        if len(set(vals))<len(vals): return False
    return True
# partial pruning: check constraints whose variables are all assigned  (only at 'last')
def dfs(i):
    nodes[0]+=1
    if time.time()-t0>lim: res['timeout']=True; return True
    if i==len(order): res['g']={f'{j},{s}':g[(j,s)] for (j,s) in g}; return True
    v=order[i]; vals=list(range(q)); rnd.shuffle(vals)
    pass
    for x in vals:
        g[v]=x
        if ok(i) and dfs(i+1): return True
    del g[v]
    return False
dfs(0)
print(json.dumps({'k':k,'nodes':nodes[0],'timeout':res.get('timeout',False),'found':'g' in res,'g':res.get('g'),'secs':round(time.time()-t0,1)}))
