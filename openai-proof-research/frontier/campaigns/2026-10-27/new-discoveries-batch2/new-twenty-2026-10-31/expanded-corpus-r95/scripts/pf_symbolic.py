import resource,json,sympy as s
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
# Homogeneity reduces Z[k,t] to univariate k with t=1. Work in QQ[k].
K=s.polys.domains.ZZ.poly_ring('k');k=K.gens[0];N=32;a=[[K.zero]*(2*N) for _ in range(2*N)]
for i in range(2*N):
 for j in range(i+1,2*N):
  a[i][j]=K.one if i==0 else (a[i-1][j]+a[i-1][j-1]+k*(-1)**i if j==i+1 else a[i-1][j]+a[i][j-1]+a[i-1][j-1]);a[j][i]=-a[i][j]
prev=K.one;o=K.one
for z in range(0,2*N,2):
 p=a[z][z+1];new,rem=divmod(p,o)
 print(json.dumps({'n':z//2+1,'pf_degree':p.degree(),'o_degree':new.degree(),'divides_over_Zk':not rem,'o_coefficients':[int(c) for c in new.to_dense()] if not rem else [],'pf_coefficients':[int(c) for c in p.to_dense()]}),flush=True)
 if rem:break
 o=new
 for i in range(z+2,2*N):
  for j in range(i+1,2*N):
   v=a[i][j]*p-a[z][i]*a[z+1][j]+a[z][j]*a[z+1][i];q,r=divmod(v,prev);assert not r;a[i][j]=q
 prev=p
