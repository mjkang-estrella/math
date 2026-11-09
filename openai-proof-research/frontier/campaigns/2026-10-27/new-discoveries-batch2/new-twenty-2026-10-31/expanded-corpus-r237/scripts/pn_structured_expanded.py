from pathlib import Path
import json,collections,itertools
L=Path(__file__).resolve().parents[1]
exec((L/'scripts/purepn.py').read_text().split('C=collections.Counter()')[0].replace('len(a)>15 or e>22','len(a)>32 or e>48'))
def iso(a,b):
 if len(a)!=len(b) or sorted(map(len,a))!=sorted(map(len,b)):return False
 n=len(a);p={};used=set()
 def rec():
  if len(p)==n:return True
  u=max((i for i in range(n) if i not in p),key=lambda i:sum(j in p for j in a[i]));cand={j for j in range(n) if j not in used and len(b[j])==len(a[u])}
  for v in a[u]:
   if v in p:cand&=b[p[v]]
  for w in cand:
   if all((v in a[u])==(p[v] in b[w]) for v in p):
    p[u]=w;used.add(w)
    if rec():return True
    used.remove(w);del p[u]
  return False
 return rec()
C=collections.Counter();hits=[];tested=0
for lengths in itertools.combinations_with_replacement(range(2,9),3):
 a,b,c=lengths;edges=[];v=2
 for d in lengths:
  path=[0]+list(range(v,v+d-1))+[1];v+=d-1;edges+=list(zip(path,path[1:]))
 G=make(v,edges)
 for n in range(max(a+b,b+c,a+c)+1,v+1):
  status,sizes=conv(G,n);tested+=1;C[status]+=1
  if status=='converge':
   h={'family':'theta','lengths':lengths,'v':v,'n':n,'edges':edges,'sizes':sizes};hits.append(h);print('HIT',h,flush=True)
 # Preserve progress even if a later instance reaches resource caps.
 (L/'outputs/pn-structured-expanded.json').write_text(json.dumps({'tested':tested,'scope':'theta graphs, each path length 2..8, n strictly greater than longest cycle and at most order','status_counts':C,'convergent_hits':hits},indent=2))
print('done',tested,dict(C),flush=True)
