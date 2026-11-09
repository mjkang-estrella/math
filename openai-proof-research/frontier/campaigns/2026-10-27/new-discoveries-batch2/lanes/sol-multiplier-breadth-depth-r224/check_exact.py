import math,json,pathlib,time
import mpmath as mp
L=pathlib.Path(__file__).resolve().parent
mp.mp.dps=150
P=600;D=1<<P
def signs(n,a,b):
 lo=hi=0
 for k in range(n,0,-1):
  c=math.comb(n,k)*math.factorial(n)//math.factorial(k)
  root=math.isqrt(k*D*D);term=c*((-a)**(k-1))*b**(n-k)
  v,w=term*root,term*(root+(root*root!=k*D*D))
  lo+=min(v,w);hi+=max(v,w)
 return 1 if lo>0 else -1 if hi<0 else 0
rows=[]
for n in [4,8,16,32,64,128]:
 c=[mp.sqrt(k)*math.comb(n,k)/math.factorial(k) for k in range(1,n+1)]
 def val(x):return mp.polyval(c[::-1],-x)
 points=[];last=None
 for j in range(3601):
  a=int(mp.mpf(10)**(-6+mp.mpf(j)*10/3600)*10**9)+1;b=10**9
  v=val(mp.mpf(a)/b);s=int(mp.sign(v))
  if s!=last:
   exact=signs(n,a,b)
   assert exact==s and exact!=0
   points.append([a,b,exact]);last=s
 assert len(points)==n,(n,len(points))
 rows.append({'degree':n,'nonzero_degree':n-1,'certified_alternating_points':points,'conclusion':'n-1 distinct negative roots of Jensen/x plus simple zero; finite degree only'})
(L/'exact-results.json').write_text(json.dumps({'sqrt_enclosure_bits':P,'rows':rows},indent=2))
print([(r['degree'],len(r['certified_alternating_points'])) for r in rows])
