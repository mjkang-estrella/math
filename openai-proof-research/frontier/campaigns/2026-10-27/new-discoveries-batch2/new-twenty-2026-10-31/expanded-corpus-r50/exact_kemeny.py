import resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(60,60))
import sympy as s,json,pathlib
p=pathlib.Path(__file__).resolve().parent;Q=s.Rational;n=11
edges=[(i,i+1) for i in range(n-1)]+[(0,2),(8,10)]
def calculate(edges):
 a=s.zeros(n)
 for u,v in edges:a[u,v]=a[v,u]=1
 d=a*s.ones(n,1);m=sum(d)/2;J=s.ones(n)/n;L=s.diag(*d)-a;B=(L+J).inv()-J;R=s.Matrix(n,n,lambda i,j:B[i,i]+B[j,j]-2*B[i,j]);K=(d.T*R*d)[0]/(4*m);rd=R*d;vals=[]
 for u in range(n):
  for v in range(u+1,n):
   if a[u,v]:continue
   z=B[:,u]-B[:,v];ds=rd[u]+rd[v]-2*m*sum(d[i]*z[i]**2 for i in range(n))+(d.dot(z))**2;val=ds/(2*m)-K/m;vals.append((val,u,v))
 val,u,v=min(vals);print('m,K,min derivative,u,v',m,K,val,u,v)
 t=s.symbols('t');At=a.copy();At[u,v]=At[v,u]=t;dt=At*s.ones(n,1);mt=sum(dt)/2;Lt=s.diag(*dt)-At;Bt=(Lt+J).inv()-J;Rt=s.Matrix(n,n,lambda i,j:Bt[i,i]+Bt[j,j]-2*Bt[i,j]);Kt=s.factor((dt.T*Rt*dt)[0]/(4*mt));print('K(t)',Kt,'derivative',s.diff(Kt,t).subs(t,0));assert s.diff(Kt,t).subs(t,0)==val
 return {'edges':edges,'nonedge':[u,v],'m':str(m),'K0':str(K),'K_t':str(Kt),'derivative':str(val),'grounded_inverse':[[str(c) for c in row] for row in B.tolist()]}
out={'barbell':calculate(edges),'path':calculate([(i,i+1) for i in range(n-1)])};(p/'exact-kemeny.json').write_text(json.dumps(out,indent=2))
