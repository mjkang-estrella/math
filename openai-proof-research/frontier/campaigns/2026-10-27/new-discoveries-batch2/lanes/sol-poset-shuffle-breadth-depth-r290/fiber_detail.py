from mechanisms import *
n=3;r={(0,1)};ps=extensions(n,r);M=matrix(n,r,ps);H=[[F(0) for p in ps] for q in ps];fibers={}
for x in range(n):
 fs={}
 for i,p in enumerate(ps):fs.setdefault(tuple(y for y in p if y!=x),[]).append(i)
 fibers[x]=[(list(k),v) for k,v in fs.items()]
 for f in fs.values():
  for i in f:
   for j in f:H[i][j]+=F(1,n*len(f))
v=[1,0,-1];norm=sum(x*x for x in v);b=F(4,9)
D=[[H[i][j]-M[i][j] for j in range(len(ps))] for i in range(len(ps))]
out=dict(relations=sorted(r),extensions=ps,M=M,H=H,vector=v,norm_squared=norm,H_rayleigh=energy(H,v)/norm,M_rayleigh=energy(M,v)/norm,target=b,target_minus_H_quadratic=b*norm-energy(H,v),H_minus_M_inertia=inertia(D),fibers=fibers,interpretation='H sharp bound fails on a genuine source-known disjoint union of chains; M retains sharp equality. No source counterexample.')
(L/'fiber-detail.json').write_text(json.dumps(out,default=str,indent=2));print(json.dumps(out,default=str))
