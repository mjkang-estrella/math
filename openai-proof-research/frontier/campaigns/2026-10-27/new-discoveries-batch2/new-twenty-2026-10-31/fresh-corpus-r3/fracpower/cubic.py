import networkx as nx, json, sys
from fracpow import frac_power, colourable
def classes(nv,target,seed=0,tries=20000):
    reps=[]
    for t in range(tries):
        G=nx.random_regular_graph(3,nv,seed=seed+t)
        if not nx.is_connected(G): continue
        if not any(nx.is_isomorphic(G,H) for H in reps): reps.append(G)
        if len(reps)>=target: break
    return reps
out=[]
for nv,target in [(8,5),(10,19)]:   # connected cubic graphs: 8 -> 5, 10 -> 19
    reps=classes(nv,target); print(nv,'classes found',len(reps),flush=True)
    for G in reps:
        for n in range(4,8):
            P=frac_power(G,3,n); w=len(max(nx.find_cliques(P),key=len)); ok=colourable(P,w)
            if not ok: rec={'nv':nv,'edges':sorted(G.edges()),'m':3,'n':n,'omega':w}; out.append(rec); print('CHI>OMEGA',rec,flush=True)
json.dump(out,open('cubic_m3.json','w'),indent=1); print('done',len(out))
