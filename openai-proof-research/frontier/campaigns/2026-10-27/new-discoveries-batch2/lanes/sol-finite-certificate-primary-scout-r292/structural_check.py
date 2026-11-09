"""Independent cut certificates for an explicit family; run under helper_guard."""
import pathlib,json
L=pathlib.Path(__file__).resolve().parent
def family(t):
 # 0=a, 1=b, 2..t+1 internal chain, t+2=c, t+3=d
 n=t+4;c=n-2;d=n-1
 positive={(0,1),(1,0),(c,d),(d,c)}|{(i,i+1) for i in range(1,c)}
 negative={(j,i) for i,j in positive if 1<=i<j<=c}|{(0,d)}
 return n,positive,negative
def closure(n,arcs):
 # Independent Floyd-Warshall, distinct from the DFS used to find the witness.
 r=[[i==j or (i,j) in arcs for j in range(n)] for i in range(n)]
 for k in range(n):
  for i in range(n):
   for j in range(n):r[i][j]=r[i][j] or (r[i][k] and r[k][j])
 return all(all(row) for row in r)
results=[]
for t in range(1,21):
 n,p,m=family(t);D=p|m;B=p|{(j,i) for i,j in m}
 assert not p&m and all(i!=j for i,j in D)
 assert len(D)==2*n-1 and closure(n,D) and closure(n,B)
 deletion=[]
 for edge in sorted(p):
  q=p-{edge}
  missing_rows=[i for i in range(n) if not any(a==i for a,b in q)]
  missing_cols=[j for j in range(n) if not any(b==j for a,b in q)]
  assert missing_rows or missing_cols
  deletion.append(dict(edge=edge,sign='+',empty_positive_rows=missing_rows,empty_positive_cols=missing_cols))
 for edge in sorted(m):
  if edge==(0,n-1):
   cut=set(range(n-2));arcs=B-{(n-1,0)};direction='incoming';which='B'
  else:
   j,i=edge;cut=set(range(i+1));arcs=D-{edge};direction='incoming';which='D'
  assert cut and len(cut)<n
  assert not any(a not in cut and b in cut for a,b in arcs)
  deletion.append(dict(edge=edge,sign='-',graph=which,cut=sorted(cut),absent=direction))
 results.append(dict(t=t,n=n,nonzeros=len(D),positive=sorted(p),negative=sorted(m),deletion_certificates=deletion))
(L/'structural-result.json').write_text(json.dumps(results,indent=2)+'\n')
print('PASS: t=1..20 independent closures and every deletion certificate; universal family proof is in PROOF.md')
