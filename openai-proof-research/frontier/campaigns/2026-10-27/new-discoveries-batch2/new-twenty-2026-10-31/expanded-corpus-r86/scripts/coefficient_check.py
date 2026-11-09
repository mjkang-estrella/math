import numpy as np,math,json
from pathlib import Path
L=Path(__file__).resolve().parents[1];N=32;rng=np.random.default_rng(86)
def mul(a,b):return np.convolve(a,b)[:N+1]
def coeff(w):
 sh=np.zeros(N+1,dtype=complex);pw=w.copy()
 for j in range(1,N+1):
  if j%2:sh+=pw/math.factorial(j)
  pw=mul(pw,w)
 a=np.zeros(N+1,dtype=complex);a[0]=1
 for n in range(1,N+1):a[n]=sum(sh[k]*a[n-k] for k in range(1,n+1))/n
 return a
best=np.zeros(N+1);witness={};count=0
for d in range(1,12):
 for shift in range(1,12):
  for a in np.linspace(-.99,.99,101):
   w=np.zeros(N+1,dtype=complex);w[shift]=a
   for k in range(1,(N-shift)//d+1):w[shift+d*k]=(1-a*a)*(-a)**(k-1)
   f=coeff(w);rat=np.abs(f)*np.arange(N+1);count+=1
   for n in range(1,N+1):
    if rat[n]>best[n]:best[n]=rat[n];witness[n]={'d':d,'shift':shift,'a':float(a),'ratio':float(rat[n])}
print(json.dumps({'scope':'Schwarz w=z^shift*(a+z^d)/(1+a*z^d), real a grid [-.99,.99],101 points; 1<=d,shift<=11; coefficient n+1 with 1<=n<=32','count':count,'best':witness,'violations':[n+1 for n in range(1,N+1) if best[n]>1+1e-9]},indent=2))
