import sys,json,itertools
T="1234 2341 2413 4231 3421 3214 2134 1243 1423 4123 1342 3412 4132 1324 3142 1432 4321 4213 3241 2314 2143 2431 4312 3124".split()
P=[tuple(int(c) for c in s) for s in T]
red=lambda t: tuple(sorted(t).index(x)+1 for x in t)
assert sorted(P)==sorted(itertools.permutations((1,2,3,4))) and len(set(P))==24
ov=all(red(P[i][1:])==red(P[(i+1)%24][:3]) for i in range(24))
# constraints: window i covers positions i..i+3 (mod 24); x[i+a] < x[i+b] iff P[i][a] < P[i][b]
N=24; edges=set()
for i,p in enumerate(P):
    for a in range(4):
        for b in range(4):
            if a!=b and p[a]<p[b]:
                u,v=(i+a)%N,(i+b)%N
                if u==v: raise SystemExit('self')
                edges.add((u,v))
# detect cycle (strict order inconsistency)
adj={u:[] for u in range(N)}
for u,v in edges: adj[u].append(v)
color=[0]*N; cyc=None
def dfs(u,st):
    global cyc
    color[u]=1; st.append(u)
    for v in adj[u]:
        if cyc: return
        if color[v]==1: cyc=st[st.index(v):]+[v]; return
        if color[v]==0: dfs(v,st)
    color[u]=2; st.pop()
for s in range(N):
    if color[s]==0 and not cyc: dfs(s,[])
# also check the lane's 9-cycle
lane=[(2,0,3),(5,0,3),(8,0,2),(10,0,3),(13,0,2),(15,0,3),(18,0,2),(20,0,3),(23,0,3)]
ok=all(P[w][a]<P[w][b] for w,a,b in lane)
chain=[((w+a)%N,(w+b)%N) for w,a,b in lane]
out={'perms_ok':True,'overlaps_ok':ov,'inconsistent':cyc is not None,'cycle_found':cyc,'lane_chain':chain,'lane_inequalities_hold':ok}
print(json.dumps(out)); json.dump(out,open(sys.argv[1],'w'),indent=1)
