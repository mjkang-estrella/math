import math,random,json
from scipy.special import erf
# p=exp(-a*y²) inside [-u,u], exp(-(a-b)u²-b*y²) outside
# normalize not needed for curvature

def conv(x,a,b,u,c,d,v):
 pts=sorted([-math.inf,-u,u,x-v,x+v,math.inf]);out=0.
 for l,h in zip(pts,pts[1:]):
  z=(l+h)/2 if math.isfinite(l*h) else (h-1 if l==-math.inf else l+1)
  A,C=(a,0) if abs(z)<u else (b,-(a-b)*u*u)
  B,D=(c,0) if abs(x-z)<v else (d,-(c-d)*v*v)
  k=A+B;m=B*x/k
  out+=math.exp(C+D-A*B*x*x/k)*math.sqrt(math.pi/k)/2*(erf(math.sqrt(k)*(h-m))-erf(math.sqrt(k)*(l-m)))
 return out
random.seed(6901);best=(1e9,None);n=0
for i in range(600):
 a=10**random.uniform(-.5,1);b=a*10**random.uniform(-2,-.05);u=random.uniform(.1,3)/math.sqrt(a)
 c=10**random.uniform(-.5,1);d=c*10**random.uniform(-2,-.05);v=random.uniform(.1,3)/math.sqrt(c)
 pars=(a,b,u,c,d,v)
 for j in range(1,31):
  x=j/6*(u+v);e=1e-3*max(1,x);r=conv(x,*pars);rp=conv(x+e,*pars);rm=conv(x-e,*pars)
  if min(r,rp,rm)<=1e-250:continue
  # logarithm squared-radius criterion x L''-L'
  L=math.log(r);dp=(math.log(rp)-math.log(rm))/(2*e);dd=(math.log(rp)+math.log(rm)-2*L)/e**2
  score=(x*dd-dp)/max(1,x);n+=1
  if score<best[0]:best=(score,(x,pars))
print(json.dumps({'checks':n,'best':best},indent=2));open('scan.json','w').write(json.dumps({'checks':n,'best':best},indent=2))
