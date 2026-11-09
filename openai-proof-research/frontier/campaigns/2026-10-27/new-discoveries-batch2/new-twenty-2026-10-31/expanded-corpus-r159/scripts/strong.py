import pathlib,json,math,itertools,time
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for n,es in json.loads((D/'outputs/atlas.json').read_text()):
 adj=[0]*n
 for a,b in es:adj[a]|=1<<b;adj[b]|=1<<a
 arb=0
 for s in range(1,1<<n):
  if s.bit_count()>1:
   e=sum((adj[v]&s).bit_count() for v in range(n) if s>>v&1)//2
   arb=max(arb,(e+s.bit_count()-2)//(s.bit_count()-1))
 k=2*arb
 es.sort(key=lambda e: -(adj[e[0]]&adj[e[1]]).bit_count())
 comps=[[1<<v for v in range(n)] for _ in range(k)];sol=[-1]*len(es)
 def rec(j,hi):
  if j==len(es):return True
  u,v=es[j]
  for c in range(min(k-1,hi+1)+1):
   A,B=comps[c][u],comps[c][v]
   if A==B:continue
   if sum((adj[w]&B).bit_count() for w in range(n) if A>>w&1)!=1:continue
   old=comps[c].copy()
   for w in range(n):
    if (A|B)>>w&1:comps[c][w]=A|B
   sol[j]=c
   if rec(j+1,max(hi,c)):return True
   comps[c]=old
  return False
 ok=rec(0,-1)
 out.append({'n':n,'edges':es,'arb':arb,'bound_colors':k,'witness':sol if ok else None})
 if not ok:print('COUNTEREXAMPLE',out[-1],flush=True)
(D/'outputs/strong-atlas.json').write_text(json.dumps(out))
print('complete',len(out),'graphs; induced-tree color classes at twice exact Nash-Williams arboricity')
