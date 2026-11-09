import json,pathlib,time,math,random
L=pathlib.Path(__file__).resolve().parent
def kernel(d,M):
 if d>=math.pi:return 0.
 a=-math.pi/2;b=math.pi/2-d;n=96;s=0.
 for k in range(n+1):
  t=a+(b-a)*k/n;v=max(0,math.cos(t+d))**M*max(0,math.cos(t))**(M-2)
  s+=v*(1 if k in (0,n) else 4 if k%2 else 2)
 return s*(b-a)/(3*n)
def gram(g,M):
 x=[0.]
 for a in g:x.append(x[-1]+a)
 return [[kernel(abs(a-b),M) for b in x] for a in x]
def mineig(A):
 n=len(A)
 for it in range(60*n*n):
  p,q=max(((i,j) for i in range(n) for j in range(i+1,n)),key=lambda ij:abs(A[ij[0]][ij[1]]))
  if abs(A[p][q])<1e-13:break
  theta=.5*math.atan2(2*A[p][q],A[q][q]-A[p][p]);c=math.cos(theta);s=math.sin(theta)
  pp,qq,pq=A[p][p],A[q][q],A[p][q]
  for k in range(n):
   if k in (p,q):continue
   ap,aq=A[k][p],A[k][q];A[k][p]=A[p][k]=c*ap-s*aq;A[k][q]=A[q][k]=s*ap+c*aq
  A[p][p]=c*c*pp-2*s*c*pq+s*s*qq;A[q][q]=s*s*pp+2*s*c*pq+c*c*qq;A[p][q]=A[q][p]=0.
 return min(A[i][i] for i in range(n))
rng=random.Random(243);rows=[]
for M in range(3,9):
 N=2*M+3;best=None
 for rep in range(160):
  g=[math.exp(rng.gauss(0,2)) for _ in range(N-1)];scale=math.pi/min(sum(g[i:i+M]) for i in range(N-M));g=[a*scale for a in g]
  A=gram(g,M);v=mineig(A)/kernel(0,M)
  if best is None or v<best['min_eigenvalue_normalized']:best={'M':M,'N':N,'min_eigenvalue_normalized':v,'gaps':g,'minimum_M_gap':min(sum(g[i:i+M]) for i in range(N-M)),'samples':160,'quadrature':'composite Simpson96, exploratory not certified'}
 rows.append(best);print(json.dumps(best),flush=True)
(L/'gram-results.json').write_text(json.dumps(rows,indent=2))
