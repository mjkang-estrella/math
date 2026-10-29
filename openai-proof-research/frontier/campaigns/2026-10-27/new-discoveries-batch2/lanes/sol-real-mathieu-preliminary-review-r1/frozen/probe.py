import cmath,math,json,pathlib
out=[]
for r in [.1,1,3,10,30,100]:
 best=(100,None)
 for rho in [.5,.9,.98,.995]:
  N=math.ceil(45/-math.log(rho))
  for k in range(1,81):
   z=cmath.rect(rho,math.pi*k/80);p=1;D=0j;A=0j
   for n in range(1,N+1):
    t=p*n/(n*n+r*r);D+=t;A+=n*t;p*=z
   v=(A/D).real
   if v<best[0]:best=(v,[rho,k,N])
 out.append({'r':r,'min':best})
print(json.dumps(out,indent=2))
