# Randomised endomorphism sampling for Conjecture 4.1 (arXiv 2202.06785) on larger non-core non-bipartite G(n,k).
# Random-order backtracking produces genuine endomorphisms (checked edge by edge); each distinct image set is tested
# for being a retract with the exact backtracking test of gp_retract_search.py. Diagnostic only (not exhaustive).
import sys, json, time, random
n=int(sys.argv[1]); k=int(sys.argv[2]); budget=float(sys.argv[3]); seed=int(sys.argv[4])
random.seed(seed)
src=open(sys.path[0]+'/gp_retract_search.py').read()
pre=src.split('# Every image contains')[0]
sys.argv=['x',str(n),str(k)]; exec(pre)
names=lambda L:[("u%d"%v if v<n else "v%d"%(v-n)) for v in L]
def random_endo(bias):
    order=[]; seen={0}; q=[0]
    while q:
        v=q.pop(0); order.append(v)
        for w in sorted(adj[v]):
            if w not in seen: seen.add(w); q.append(w)
    a={}
    def rec(i):
        if i==N: return True
        v=order[i]; D=(1<<N)-1
        for w in adj[v]:
            if w in a: D&=nb[a[w]]
        cand=bits(D)
        # bias towards re-using already-used values (to get small images)
        used=set(a.values())
        random.shuffle(cand)
        if random.random()<bias: cand.sort(key=lambda x: x not in used)
        for x in cand:
            a[v]=x
            if rec(i+1): return True
            del a[v]
        return False
    sys.setrecursionlimit(10000)
    rec(0)
    for x in range(N):
        for y in adj[x]: assert a[y] in adj[a[x]]
    return a
t=time.time(); samples=0; images={}; bad=[]
while time.time()-t<budget:
    f=random_endo(random.choice([0,0.5,0.8,0.95,1.0]))
    S=0
    for v in range(N): S|=1<<f[v]
    samples+=1
    cs=min(apply(p,S) for p in perms)
    if cs in images: continue
    r=is_hom_search(cs, True, False)
    images[cs]=r
    if not r: bad.append(names(bits(cs)))
sizes={}
for S in images: sizes[bin(S).count('1')]=sizes.get(bin(S).count('1'),0)+1
print(json.dumps({'n':n,'k':k,'seed':seed,'samples':samples,'distinct_image_classes':len(images),'image_size_histogram':dict(sorted(sizes.items())),'nonretract_images':bad[:5],'num_nonretract_images':len(bad),'secs':round(time.time()-t,1)}))
