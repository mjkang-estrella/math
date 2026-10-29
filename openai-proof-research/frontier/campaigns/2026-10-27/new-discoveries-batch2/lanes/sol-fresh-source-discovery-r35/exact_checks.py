"""Exact diagnostics of the failed contraction attack; not a source proof."""
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(40,40))
import itertools,json,math,time
from fractions import Fraction as Q
from pathlib import Path

def det(a):
 a=[r[:] for r in a]; ans=Q(1)
 for i in range(len(a)):
  pivot=next((j for j in range(i,len(a)) if a[j][i]),None)
  if pivot is None:return Q(0)
  if pivot!=i:a[i],a[pivot]=a[pivot],a[i];ans=-ans
  v=a[i][i];ans*=v
  for j in range(i+1,len(a)):
   c=a[j][i]/v
   if c:
    for k in range(i+1,len(a)):a[j][k]-=c*a[i][k]
   a[j][i]=0
 return ans

def run():
 start=time.monotonic(); records=[]
 # L_A=256 product of its four coordinates: other node types have <=3 support.
 for m in range(4,8):
  sets=list(map(frozenset,itertools.combinations(range(m),4)))
  for t in [Q(0),Q(1,4),Q(1,2),Q(1)]:
   a=(1-t)/4;b=t/m
   mat=[]
   for A in sets:
    row=[]
    for B in sets:
     r=len(A&B)
     direct=Q(256)*(a+b)**r*b**(4-r)
     expansion=sum(Q(256)*a**j*b**(4-j)*math.comb(r,j) for j in range(r+1))
     assert direct==expansion
     row.append(direct)
    mat.append(row)
   d=det(mat); diag=(1-t+4*t/m)**4
   assert 0<=d<=diag**len(sets)<=1
   if m>4 and t>0:assert d<1
   if t==0:assert d==1
   records.append({'m':m,'tau':str(t),'nodes_moved':len(sets),'det_numerator':str(d.numerator),'det_denominator':str(d.denominator)})
 # Published K(c)>1: certify sqrt5 by rational bounds, not floats.
 lo,hi=Q(2236,1000),Q(2237,1000)
 assert lo**2<5<hi**2
 kl=(80243*lo+9298842)/9453125
 assert kl>1
 # Generic determinant lemma derivative for a mixture has N(K-1).
 # At dimension4 N=70; evaluate a rational lower bound at small epsilon.
 N=70;eps=Q(1,1000000)
 lower=(1-eps)**(N-1)*(1-eps+eps*N*kl)
 assert lower>1
 out={'status':'PASS: finite identities for a proved failed-route obstruction only','records':records,'centroid_K_lower':str(kl),'weighted_design_ratio_lower':str(lower),'elapsed_seconds':time.monotonic()-start,'limits':{'address_space_MiB':512,'cpu_seconds':40,'external_wall_seconds':55,'maximum_matrix_size':35},'source_resolution':False}
 (Path(__file__).parent/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))
if __name__=='__main__':run()
