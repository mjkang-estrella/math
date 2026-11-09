import json
from pathlib import Path
w=Path(__file__).parent;c=json.loads((w/'spectral_candidate.json').read_text())
def cp(a):
 n=len(a);b=[[int(i==j) for j in range(n)] for i in range(n)];out=[1]
 for k in range(1,n+1):
  b=[[sum(a[i][t]*b[t][j] for t in range(n)) for j in range(n)] for i in range(n)]
  tr=sum(b[i][i] for i in range(n));assert tr%k==0;v=-tr//k;out.append(v)
  for i in range(n):b[i][i]+=v
 return out
def matrices(edges):
 n=c['n'];a=[[0]*n for _ in range(n)]
 for u,v in edges:a[u][v]=a[v][u]=1
 co=[[int(i!=j)-a[i][j] for j in range(n)] for i in range(n)]
 line=[[int(i!=j and bool(set(e)&set(f))) for j,f in enumerate(edges)] for i,e in enumerate(edges)]
 return dict(adjacency=a,complement=co,line=line)
m={x:matrices(c[x]) for x in ['g','h']};r={}
for kind in m['g']:
 p,q=cp(m['g'][kind]),cp(m['h'][kind]);r[kind]=dict(g=p,h=q,equal=p==q);print(kind,p==q,p)
(w/'exact_spectra.json').write_text(json.dumps(r,indent=2))
