import math,json
N=1000;arrays=0;rational=0;triples=[]
for k in range(2,N+1):
 for r in range(2,k+2):
  for c in range(1,k//(r-1)+1):
   if k-c-1<0 or k-(r-1)*c-1<0:continue
   arrays+=1;delta=k-1-r*c;d=math.isqrt(delta*delta+4*k)
   if d*d!=delta*delta+4*k or (d-delta)%2:continue
   s=(d-delta)//2;rational+=1
   for gamma in [0,1]:
    # eq: alpha*r*(-s)+(1-gamma)*(-(r-1)*s+k)+gamma*(s+k)=0
    numer=(1-gamma)*(k-(r-1)*s)+gamma*(s+k)
    if numer<0 or numer%(r*s):continue
    alpha=numer//(r*s)
    if alpha<=k-c-1 and gamma-alpha>-s+k-c-1 and alpha!=gamma:
     triples.append([k,r,c,s,alpha,1-gamma,gamma])
out={'max_valency':N,'parameter_arrays_tested':arrays,'integer_least_root_arrays':rational,'surviving_triples':triples,'scope':'antipodal diameter-three parameter superset; no graph existence asserted'}
open('outputs/antipodal.json','w').write(json.dumps(out,indent=2));print({**out,'surviving_triples_count':len(triples),'surviving_triples':triples[:10]})
