import pathlib,decimal,math,itertools,json,resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));decimal.getcontext().prec=45;D=decimal.Decimal
from slab_diagnostic import volume
# Inclusion-exclusion for positive weights, total width t in unit cube.
def vol(ws,t):
 norm=sum(w*w for w in ws).sqrt();ws=[w/norm for w in ws];k=len(ws);s=(sum(ws)+t)/2
 total=D(0)
 for mask in range(1<<k):
  z=s-sum((ws[j] for j in range(k) if mask>>j&1),D(0))
  if z>0:total+=(-1)**mask.bit_count()*z**k
 return 2*total/(D(math.factorial(k))*math.prod(ws))-1
hits=[];best=None
for it in range(85,181,5):
 t=D(it)/100;named=min(volume(k,t) for k in [2,3,5])
 for m in [2,3,4]:
  for ir in range(1,41):
   r=D(ir)/20;v=vol([D(1)]*m+[r],t);gap=named-v
   row=dict(t=str(t),ones=m,last=str(r),gain=str(gap))
   if best is None or gap>D(best['gain']):best=row
   if gap>D('1e-30'):hits.append(row)
print(json.dumps(dict(status='diagnostic_only',shape='m equal positive weights and one variable positive weight, normalized',n=5,t_grid='0.85..1.80 step0.05',ratio_grid='0.05..2 step0.05',strict_improvements=hits,best=best),indent=2))
