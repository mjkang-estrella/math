from pathlib import Path
import json
p=Path(__file__).parent;gs=json.loads((p/'search-input.json').read_text());es=json.loads((p/'rooted-equalities.json').read_text());bad=[]
def rooted_iso(i,r,j,s):
 A,B=gs[i],gs[j]
 if A['n']!=B['n'] or len(A['edges'])!=len(B['edges']):return False
 n=A['n'];a=[set() for _ in range(n)];b=[set() for _ in range(n)]
 for G,adj in [(A,a),(B,b)]:
  for u,v in G['edges']:adj[u].add(v);adj[v].add(u)
 if len(a[r])!=len(b[s]):return False
 mapping={r:s};used={s};order=sorted((v for v in range(n) if v!=r),key=lambda v:-len(a[v]))
 def rec(t):
  if t==len(order):return True
  v=order[t]
  for w in range(n):
   if w in used or len(a[v])!=len(b[w]) or any((u in a[v])!=(z in b[w]) for u,z in mapping.items()):continue
   mapping[v]=w;used.add(w)
   if rec(t+1):return True
   used.remove(w);del mapping[v]
  return False
 return rec(0)
for i,r,j,u in es:
 if not rooted_iso(i,r,j,u):bad.append([i,r,j,u])
res=dict(equalities=len(es),nonisomorphic=bad,all_equalities_within_same_graph=all(i==j for i,r,j,u in es));(p/'rooted-isomorphism-check.json').write_text(json.dumps(res,indent=2));print(res)
