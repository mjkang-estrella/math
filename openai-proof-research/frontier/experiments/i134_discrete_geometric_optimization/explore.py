"""Floating Gaussian-wave observations, deliberately not an analytic certificate."""
import math,json

def run():
 a=math.sqrt(2/math.sqrt(3));eta=.05;rows=[]
 for alpha in [.5,1.,2.]:
  for m in [4,8,16,32]:
   delta=0.
   for j in range(-12,13):
    for k in range(-12,13):
     if j==k==0:continue
     x=a*(j+k/2);y=a*math.sqrt(3)*k/2
     base=math.exp(-math.pi*alpha*(x*x+y*y))
     for z in range(m):
      shift=eta*(math.sin(2*math.pi*(z+j)/m)-math.sin(2*math.pi*z/m))
      delta+=(math.exp(-math.pi*alpha*((x+shift)**2+y*y))-base)/m
   rows.append(dict(alpha=alpha,m=m,eta=eta,truncated_excess=delta,m_squared_excess=m*m*delta,label_variance=eta*eta/2))
 return {'arithmetic':'IEEE floating point','shell':'integer lattice coefficients j,k in [-12,12]','tail':'not certified by this computation; the report proves the infinite-sum bound analytically','rows':rows,'scope':'observations only, not exact energy or universal certification'}
if __name__=='__main__':print(json.dumps(run(),indent=2))
