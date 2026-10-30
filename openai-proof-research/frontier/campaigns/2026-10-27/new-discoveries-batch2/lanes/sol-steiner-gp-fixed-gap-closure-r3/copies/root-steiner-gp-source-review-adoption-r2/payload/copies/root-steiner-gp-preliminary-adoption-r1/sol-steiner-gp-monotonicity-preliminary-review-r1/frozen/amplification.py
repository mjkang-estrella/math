from pathlib import Path
import itertools,json,collections
L=Path(__file__).resolve().parent
def base():
 # 0=w, 1,2,3=rim; spokes get one internal vertex; rim edges get two.
 e=[];v=4
 for i in range(1,4):e.extend([(0,v),(v,i)]);v+=1
 for a,b in [(1,2),(2,3),(3,1)]:e.extend([(a,v),(v,v+1),(v+1,b)]);v+=2
 return v,e
def build(m):
 n,e=base();classes=[];p=0
 for i in range(n):
  q=list(range(p,p+(m if i<4 else 1)));classes.append(q);p+=len(q)
 E=[(u,v) for a,b in e for u in classes[a] for v in classes[b]]
 adj=[set() for _ in range(p)]
 for a,b in E:adj[a].add(b);adj[b].add(a)
 return classes,E,adj
def run():
 C,E,adj=build(10);n=len(adj);D=[]
 for v in range(n):
  d=[n+1]*n;d[v]=0;q=collections.deque([v])
  while q:
   u=q.popleft()
   for w in adj[u]:
    if d[w]>d[u]+1:d[w]=d[u]+1;q.append(w)
  D.append(d)
 A=sum(C[:4],[]);triples=0
 for a,b,c in itertools.combinations(A,3):
  assert D[a][b]+D[b][c]>D[a][c]
  assert D[a][c]+D[c][b]>D[a][b]
  assert D[b][a]+D[a][c]>D[b][c];triples+=1
 count=0
 for a,b,c in itertools.product(*C[1:4]):
  # For three terminals a tree median gives exact Steiner edge count.
  cost=min(D[v][a]+D[v][b]+D[v][c] for v in range(n));assert cost==6
  for w in C[0]:assert D[w][a]+D[w][b]+D[w][c]==6
  count+=1
 from checks import tables,good,values
 nb,eb=base();cost,U=tables(nb,eb);orig=15
 assert good(orig,2,U) and not good(orig,3,U)
 result=dict(n=n,edges=E,classes=C,gp_candidate=A,gp_triples=triples,rim_triples=count,center_choices=10,
  gp_lower=40,sgp3_upper=39,base_n=nb,base_values=values(nb,eb),
  note='Exact finite diagnostics corroborate the ordinary proof; upper bound uses the proved four-class obstruction, not subset enumeration on 49 vertices.')
 (L/'amplification.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k not in ['edges','classes','gp_candidate']})
if __name__=='__main__':run()
