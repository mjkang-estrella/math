import os,resource,json,math
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(40,)*2)
from pathlib import Path
N=300
A=[];B=[]
for n in range(N+2):
 if n%2:A.append(0)
 else:
  v=4**n-sum(math.comb(n,k)*17**(k//2) for k in range(0,n+1,2))+5*sum(math.comb(n,k)*17**((k-1)//2) for k in range(1,n+1,2))
  assert v%2==0;A.append(v//2)
 if n%2==0:B.append(0)
 else:
  v=sum(math.comb(n,k)*(5**k-17**(k//2)) for k in range(0,n+1,2))
  assert v%2==0;B.append(v//2)
U=[];V=[]
for n in range(N):
 U.append(sum(math.comb(n,k)*(B[k+1]*A[n-k]-B[k]*A[n-k+1]-A[k]*A[n-k]) for k in range(n+1)))
 V.append(-4*sum(math.comb(n,k)*B[k]*A[n-k] for k in range(n+1)))
E=[U[n]+(n*V[n-1] if n else 0)+(2*n*(n-1)*U[n-2] if n>=2 else 0) for n in range(N)]
assert all(E[n]==0 for n in range(10));assert all(E[n]>0 for n in range(10,N,2));assert all(E[n]==0 for n in range(1,N,2))
p=Path(__file__).parent
other=json.loads((p/'expchecks.json').read_text())['coefficients']
assert all(r['sqrt17']=='0' and E[r['n']]==int(r['rational']) for r in other)
(p/'integer-certificate.json').write_text(json.dumps({'status':'PASS','method':'independent integer derivative convolution','E_derivatives':{str(n):str(E[n]) for n in range(0,N,2)}},indent=2))
print('PASS independent integer coefficient certificate; zeros n<10, positive even 10..298; agrees with exponential-field method')
