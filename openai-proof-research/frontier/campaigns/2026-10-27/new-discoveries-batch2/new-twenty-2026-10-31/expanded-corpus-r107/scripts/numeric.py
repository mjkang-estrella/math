import pathlib,json,sys,math,time
from fractions import Fraction as F
D=pathlib.Path(__file__).resolve().parents[1];mode=sys.argv[1];out=[]
def emit(o):
 out.append(o);print(o,flush=True);(D/'outputs'/f'{mode}.json').write_text(json.dumps(out,indent=2)+'\n')
if mode=='hurwitz':
 def pol(n):return [k*(n-k)*math.comb(2*n+2,2*k+1)//(4*n+2) for k in range(n)]
 def conv(a,b):
  r=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):r[i+j]+=x*y
  return r
 for n in range(1,101):
  a=conv(pol(n+1),pol(n+1));b=conv(pol(n+2),pol(n));c=[x-(b[j] if j<len(b) else 0) for j,x in enumerate(a)]
  while c and c[0]==0:c.pop(0)
  while c and c[-1]==0:c.pop()
  # Exact Routh array of descending polynomial. Positive first column certifies strict stability after zero root removal.
  r=list(map(F,c[::-1]));r0=r[::2];r1=r[1::2]+[F(0)]*(len(r0)-len(r[1::2]));signs=[r0[0]>0,r1[0]>0];deg=len(c)-1;exception=None
  for k in range(deg-1):
   if not r1[0]:exception='zero pivot';break
   rr=[(r1[0]*r0[j+1]-r0[0]*r1[j+1])/r1[0] for j in range(len(r0)-1)]+[F(0)]
   r0,r1=r1,rr;signs.append(r1[0]>0)
  emit({'n':n,'degree_after_zero_roots':deg,'all_Routh_pivots_positive':all(signs),'exception':exception})
if mode=='partitions':
 def bareiss(A):
  A=[r[:] for r in A];prev=1;sgn=1
  for k in range(len(A)-1):
   if A[k][k]==0:
    z=next((i for i in range(k+1,len(A)) if A[i][k]),None)
    if z is None:return 0
    A[k],A[z]=A[z],A[k];sgn=-sgn
   pivot=A[k][k]
   for i in range(k+1,len(A)):
    for j in range(k+1,len(A)):A[i][j]=(A[i][j]*pivot-A[i][k]*A[k][j])//prev
   prev=pivot
  return sgn*A[-1][-1]
 N=6500
 for k,threshold in [(1,[1,1,20,84,194,362,594,890,1258,1700,2218,2818,3498,4264]),(2,[1,1,18,72,168,308,506,762,1082,1464,1914,2436,3028,3696])]:
  sig=[0]*(N+1)
  for d in range(1,N+1):
   exponent=3-(d%2==0)-(d%(2*k+1)==0)+(d%(4*k+2)==0)
   for j in range(d,N+1,d):sig[j]+=d*exponent
  a=[1]+[0]*N
  for n in range(1,N+1):
   v=sum(sig[j]*a[n-j] for j in range(1,n+1));assert v%n==0;a[n]=v//n
  for m,T in enumerate(threshold,1):
   tested=sorted(set(range(max(T,m-1),max(T,m-1)+51))|{T+100,T+500,T+1000,6000})
   vals=[bareiss([[a[n-i+j] for j in range(m)] for i in range(m)]) for n in tested]
   bad=[n for n,v in zip(tested,vals) if v<0];emit({'k':k,'m':m,'threshold':T,'tested_n':tested,'negative':bad,'min_sign':min((v>0)-(v<0) for v in vals)})
if mode=='schur':
 N=70000;a=[0]*(N+1);a[0]=1
 # Euler product with allowed part residues 0,1,5 mod6. Fast logarithmic recurrence mod32 using exact coefficients is expensive; product DP in C++ separate.
