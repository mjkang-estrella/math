from pathlib import Path
import sys,math,json
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'.pydeps'))
from flint import fmpz_poly,fmpq_poly
import mpmath as mp
mp.mp.dps=120
x=fmpz_poly([0,1])

def polys(k):
 A=[1]+[0]*(k+2)
 for t in range(1,k+2):
  A=[0]+[(k*j-t+1)*A[j]+k*A[j-1] for j in range(1,k+3)]
 # A=(k-1)! C(k,k+1,j)
 fact=math.factorial(k-1)
 rho=fmpz_poly([0]); y=x**k; ym=y-1; ymK=ym**k
 sig=fmpz_poly([0]); S=fmpz_poly([1]*k); SK=S**k
 for j in range(k):
  n=math.factorial(j)*A[j+2]; assert n%fact==0
  rho+=(-1)**j*(n//fact)*(ym**(k-j-1)*y**(j+1)-ymK)
  sig+=(-1)**j*math.comb(k+1,j+2)*(x**(j+1)*(x-1)**(k-j-1)*SK-ymK)
 return rho,sig

def mobius(p,n):
 a=[p[i]for i in range(n+1)]
 a=list(reversed(a))
 q=fmpz_poly(a)(x+1)
 return list(reversed([int(q[i])for i in range(n+1)]))

def alpha(k):
 lo=mp.mpf(0);hi=mp.mpf(1)
 for _ in range(450):
  mid=(lo+hi)/2
  if mid*(1+mid)**(k-1)>1:hi=mid
  else:lo=mid
 return(lo+hi)/2

if __name__ == "__main__":
 for k in range(2,int(sys.argv[1])+1):
  r,s=polys(k);n=k*k-1;u,v=mobius(r,n),mobius(s,n);a=alpha(k)
  signs=[]
  for i,(uu,vv)in enumerate(zip(u,v)):
   t=a*uu-vv
   if t:signs.append((i,mp.sign(t)))
  trans=[signs[0]]+[signs[i]for i in range(1,len(signs))if signs[i][1]!=signs[i-1][1]]
  print(json.dumps({'k':k,'degree':n,'alpha':str(a),'mobius_sign_variations':len(trans)-1,'blocks':[(i,int(z))for i,z in trans]}),flush=True)
