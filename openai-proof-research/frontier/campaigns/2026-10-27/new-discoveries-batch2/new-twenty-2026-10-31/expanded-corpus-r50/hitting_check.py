import resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(60,60))
import sympy as s,json,pathlib
p=pathlib.Path(__file__).resolve().parent;data=json.load(open(p/'exact-kemeny.json'));out={};n=11
for name,x in data.items():
 A=s.zeros(n);E=s.zeros(n);u,v=x['nonedge'];E[u,v]=E[v,u]=1
 for i,j in x['edges']:A[i,j]=A[j,i]=1
 d=A*s.ones(n,1);e=E*s.ones(n,1);vol=sum(d);P=s.diag(*[1/z for z in d])*A;Pd=s.diag(*[1/z for z in d])*E-s.diag(*[e[i]/d[i]**2 for i in range(n)])*A
 H=s.zeros(n);Hd=s.zeros(n)
 for j in range(n):
  ids=[i for i in range(n) if i!=j];M=s.eye(n-1)-P.extract(ids,ids);h=M.inv()*s.ones(n-1,1);hp=M.inv()*Pd.extract(ids,ids)*h
  for i,hi,hpi in zip(ids,h,hp):H[i,j]=hi;Hd[i,j]=hpi
 pi=d/vol;pid=e/vol-d*sum(e)/vol**2;K=H*pi;Kd=Hd*pi+H*pid;assert all(z==s.Rational(x['K0']) for z in K);assert all(z==s.Rational(x['derivative']) for z in Kd)
 out[name]={'H':[[str(z) for z in row] for row in H.tolist()],'Hprime':[[str(z) for z in row] for row in Hd.tolist()],'stationary':[str(z) for z in pi],'stationary_prime':[str(z) for z in pid],'K_all_start_states':[str(z) for z in K],'Kprime_all_start_states':[str(z) for z in Kd]};print(name,K[0],Kd[0],flush=True)
(p/'hitting-certificate.json').write_text(json.dumps(out,indent=2));print('difference',s.Rational(data['path']['derivative'])-s.Rational(data['barbell']['derivative']))
