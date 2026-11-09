import sys,json
n=12
E=[(i,(i+1)%n) for i in range(n)]+[(i,i+6) for i in range(6)]
lab=[17,13,7,8,3,15,6,18,4,5,12,2,10,1,9,16,14,11]
assert sorted(lab)==list(range(1,19)) and len(E)==18 and len(set(frozenset(e) for e in E))==18
S=[0]*n
for (u,v),l in zip(E,lab): S[u]+=l; S[v]+=l
proper=all(S[u]!=S[v] for u,v in E)
# Mobius ladder check: cycle 0..11 with chords i~i+6 is M_12 (u1..u6 v1..v6 cycle plus u_i v_i)
out={'sums':S,'proper':proper,'distinct':sorted(set(S)),'num_colors':len(set(S))}
# also: 3 is a lower bound? M_12 has odd cycles? chromatic number of M_12 (n=6 even): M_{2n} with n even is bipartite? check
import itertools
adj={i:set() for i in range(n)}
for u,v in E: adj[u].add(v); adj[v].add(u)
col={0:0}; st=[0]; bip=True
while st:
    x=st.pop()
    for y in adj[x]:
        if y not in col: col[y]=1-col[x]; st.append(y)
        elif col[y]==col[x]: bip=False
out['bipartite']=bip
print(json.dumps(out)); json.dump(out,open(sys.argv[1],'w'),indent=1)
