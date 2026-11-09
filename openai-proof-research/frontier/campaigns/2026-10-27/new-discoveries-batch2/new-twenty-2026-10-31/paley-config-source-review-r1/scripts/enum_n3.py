# Exhaustive enumeration of all labeled 9_3 configurations on points 0..8 (independent of author code).
# For each: #triangles (3 lines pairwise meeting in 3 distinct points), #parallel pairs,
# max pairwise-intersecting line set, min monochromatic triangles over line 2-colourings.
import itertools, json, collections, time
t0=time.time()
import sys; N=int(sys.argv[1])
pairs_ok=lambda used,l: all(((min(a,b),max(a,b)) not in used) for a,b in itertools.combinations(l,2))
res=collections.Counter(); examples={}
def analyse(lines):
    m=len(lines); bits=[sum(1<<p for p in l) for l in lines]
    meet=[[bin(bits[i]&bits[j]).count('1') for j in range(m)] for i in range(m)]
    tris=[]
    for i,j,k in itertools.combinations(range(m),3):
        if meet[i][j] and meet[i][k] and meet[j][k] and not (bits[i]&bits[j]&bits[k]):
            tris.append((1<<i)|(1<<j)|(1<<k))
    par=sum(1 for i,j in itertools.combinations(range(m),2) if not meet[i][j])
    adj=[sum(1<<j for j in range(m) if j!=i and meet[i][j]) for i in range(m)]
    best=0
    for S in range(1<<m):
        c=bin(S).count('1')
        if c<=best: continue
        ok=True; s=S
        while s:
            i=(s&-s).bit_length()-1; s&=s-1
            if (S & ~(1<<i)) & ~adj[i]: ok=False; break
        if ok: best=c
    mn=99
    full=(1<<m)-1
    for c in range(1<<(m-1)):  # colour symmetry: fix colour of line m-1
        cnt=0
        for t in tris:
            x=c&t
            if x==0 or x==t:
                cnt+=1
                if cnt>=mn: break
        if cnt<mn: mn=cnt
        if mn==0: break
    return (len(tris),par,best,mn)
count=0
def rec(lines,deg,used):
    global count
    p=next((x for x in range(N) if deg[x]<3),None)
    if p is None:
        count+=1
        key=analyse(lines); res[key]+=1
        examples.setdefault(str(key),[list(l) for l in lines]); return
    last=max((l for l in lines if l[0]==p),default=None)
    for a,b in itertools.combinations(range(p+1,N),2):
        l=(p,a,b)
        if last is not None and l<=last: continue
        if deg[a]>=3 or deg[b]>=3 or not pairs_ok(used,l): continue
        for x in l: deg[x]+=1
        nu=used|{(p,a),(p,b),(a,b)}
        rec(lines+[l],deg,nu)
        for x in l: deg[x]-=1
rec([], [0]*N, frozenset())
out={'total_labeled':count,'classes':{str(k):v for k,v in res.items()},'key':'(n_triangles,n_parallel_pairs,max_pairwise_intersecting,min_mono)',
     'expected_labeled_from_known_aut_orders_108_9_12':None,'examples':examples,'seconds':time.time()-t0}
print(json.dumps({k:v for k,v in out.items() if k!='examples'},indent=1))
json.dump(out,open('checks/enum'+str(N)+'_3.json','w'),indent=1)
