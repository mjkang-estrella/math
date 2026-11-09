import networkx as nx,json,pathlib,time
from fractions import Fraction
D=pathlib.Path(__file__).resolve().parents[1]
def score(g):
 def dp(v,p):
  z={(0,0):(1,0),(1,0):(1,1)}
  for w in g[v]:
   if w==p:continue
   b=dp(w,v); zz={}
   for (s,k),(c,t) in z.items():
    for (r,l),(d,u) in b.items():
     h=k+l+s*r
     if h>1:continue
     old=zz.get((s,h),(0,0));zz[s,h]=(old[0]+c*d,old[1]+t*d+c*u)
   z=zz
  return z
 z=dp(0,-1);c=sum(v[0] for k,v in z.items() if k[1]==1);t=sum(v[1] for k,v in z.items() if k[1]==1)
 return Fraction(t,c)
if __name__=='__main__':
 rows=[]
 for n in range(4,17):
  r=nx.star_graph(n-2);r.add_edge(1,n-1);target=score(r);best=Fraction(0);count=0;edges=None
  for g in nx.nonisomorphic_trees(n):
   s=score(g);count+=1
   if s>best:best=s;edges=list(g.edges())
  row=dict(n=n,trees=count,target=str(target),maximum=str(best),counterexample_edges=edges if best>target else None);rows.append(row);print(row,flush=True)
 (D/'outputs/trees.json').write_text(json.dumps(rows,indent=2)+'\n')
