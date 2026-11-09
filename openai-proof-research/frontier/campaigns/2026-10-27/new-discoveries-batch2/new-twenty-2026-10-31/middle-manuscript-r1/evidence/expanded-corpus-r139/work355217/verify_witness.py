# Independent verifier (set-based, no bitmasks) for the n=8 witness of 355217.
import itertools, json
V=list(range(8))
E=[(0,1),(0,6),(1,6),(2,3),(2,7),(3,7),(4,6),(4,7),(5,6),(5,7),(6,7)]
def graph(Vs,Es):
    N={v:set() for v in Vs}
    for a,b in Es: N[a].add(b); N[b].add(a)
    return N
def is_conn(N,keep):
    keep=set(keep)
    if not keep: return True
    st=[next(iter(keep))]; seen={st[0]}
    while st:
        v=st.pop()
        for w in N[v]:
            if w in keep and w not in seen: seen.add(w); st.append(w)
    return seen==keep
def ocd_sets(N,k):
    Vs=list(N)
    for S in itertools.combinations(Vs,k):
        S=set(S)
        if all(v in S or N[v]&S for v in Vs) and is_conn(N,set(Vs)-S): yield S
G=graph(V,E)
gG=next(k for k in range(1,9) if any(True for _ in ocd_sets(G,k)))
MV=[('v',v) for v in V]+[('e',e) for e in E]
ME=[(('v',a),('e',(a,b))) for a,b in E]+[(('v',b),('e',(a,b))) for a,b in E]
ME+=[(('e',e),('e',f)) for e,f in itertools.combinations(E,2) if set(e)&set(f)]
M=graph(MV,ME)
gM=next(k for k in range(1,len(MV)+1) if any(True for _ in ocd_sets(M,k)))
wit=[sorted(map(str,S)) for S in ocd_sets(M,gM)]
print(json.dumps({'connected_G':is_conn(G,set(V)),'n':8,'m':len(E),'ocd_G':gG,'ocd_M':gM,'M_order':len(MV),
  'ocd_sets_G_min':[sorted(S) for S in ocd_sets(G,gG)],'num_min_sets_M':len(wit),'witness_sets_M':wit[:6]},indent=0))
