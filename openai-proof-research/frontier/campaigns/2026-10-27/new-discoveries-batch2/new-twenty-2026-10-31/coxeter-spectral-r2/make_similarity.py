from pathlib import Path
import sys,json,random
w=Path(__file__).resolve().parent
sys.path.insert(0,str(w.parent/'fresh-corpus-r10/pydeps'))
import sympy as s
c=json.loads((w.parent/'fresh-corpus-r10/spectral_candidate.json').read_text());a=[]
for k in ['g','h']:
 E=c[k];A=s.zeros(19)
 for u,v in E:A[u,v]=A[v,u]=1
 L=s.zeros(18)
 for i,e in enumerate(E):
  for j,f in enumerate(E):L[i,j]=int(i!=j and bool(set(e)&set(f)))
 a.append([A,s.ones(19)-s.eye(19)-A,L])
r={};rng=random.Random(330264)
for j,name in enumerate(['adjacency','complement','line']):
 A,B=a[0][j],a[1][j];n=A.rows
 for seed in range(4):
  v=s.Matrix([rng.randrange(-2,3) for i in range(n)]);ka=[v];kb=[v]
  for i in range(1,n):ka.append(A*ka[-1]);kb.append(B*kb[-1])
  KA=s.Matrix.hstack(*ka);KB=s.Matrix.hstack(*kb)
  if KA.det()!=0 and KB.det()!=0:
   P=KA*KB.inv();Q=P.inv();assert A*P==P*B and P*Q==s.eye(n)
   r[name]={'P':[[str(x) for x in P.row(i)] for i in range(n)],'Q':[[str(x) for x in Q.row(i)] for i in range(n)]};print(name,'OK',flush=True);break
 else: print(name,'NO CYCLIC VECTOR',flush=True)
(w/'similarity.json').write_text(json.dumps(r,indent=2))
