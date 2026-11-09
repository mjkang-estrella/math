# Full reduced claim: for s<=t<=N-s, injection L_s -> L_t with phi(x) in D(x)=prod [m_i, c_i-m_i], m_i=min(x_i,c_i-x_i).
import itertools,sys
sys.setrecursionlimit(100000)
def match(U,V,ok):
    Vi={v:i for i,v in enumerate(V)}; mt=[None]*len(V)
    adj={u:[Vi[v] for v in V if ok(u,v)] for u in U}
    def aug(u,seen):
        for j in adj[u]:
            if j in seen: continue
            seen.add(j)
            if mt[j] is None or aug(mt[j],seen): mt[j]=u; return True
        return False
    return sum(1 for u in U if aug(u,set()))
maxc=int(sys.argv[1]); maxB=int(sys.argv[2]); maxlev=int(sys.argv[3])
bad=0;cnt=0
for B in range(1,maxB+1):
    for c in itertools.combinations_with_replacement(range(1,maxc+1),B):
        L={}
        for x in itertools.product(*[range(ci+1) for ci in c]): L.setdefault(sum(x),[]).append(x)
        N=sum(c)
        def ok(x,y):
            return all(min(a,ci-a)<=b<=ci-min(a,ci-a) for a,b,ci in zip(x,y,c))
        for s in range(0,N//2+1):
            if len(L[s])>maxlev: continue
            for t in range(s+1,N-s+1):
                if len(L[t])>maxlev*3: continue
                m=match(L[s],L[t],ok); cnt+=1
                if m<len(L[s]): bad+=1; print('FAIL',c,s,t,len(L[s]),m,flush=True)
print('cases',cnt,'fail',bad)
