from pathlib import Path
from math import factorial,comb
from fractions import Fraction as F
import json,hashlib,time
L=Path(__file__).resolve().parent
def q(m):return [F((-1)**j*comb(m,j)*factorial(2*m-j),factorial(2*m)) for j in range(m+1)]
def inverse(q,N):
 c=[F(1)]
 for n in range(1,N+1):c.append(-sum(q[j]*c[n-j] for j in range(1,min(n,len(q)-1)+1)))
 return c
def sweep(m,N):
 D=factorial(2*m);a=[(-1)**j*comb(m,j)*factorial(2*m-j) for j in range(m+1)]
 b=[a[j]*D**(j-1) for j in range(1,m+1)];C=[1]
 for n in range(1,N+1):C.append(-sum(b[j-1]*C[n-j] for j in range(1,min(m,n)+1)))
 # C_n=D^n c_n, independently compare exact Fraction coefficients at low indices.
 c=inverse(q(m),12)
 assert all(F(C[n],D**n)==c[n] for n in range(13))
 return {'m':m,'n_max':N,'nonpositive':[n for n,x in enumerate(C) if x<=0],'last_bits':C[-1].bit_length(),'integer_stream_sha256':hashlib.sha256(b''.join(x.to_bytes((x.bit_length()+8)//8,'big',signed=True)+b'\0' for x in C)).hexdigest()}
start=time.monotonic();rows=[sweep(m,400) for m in range(1,40,2)]
for m in range(2,42):
 a,b,c=q(m),q(m-1),q(m-2);k=F(1,4*(2*m-1)*(2*m-3))
 assert all(a[j]==(b[j] if j<len(b) else 0)+(k*c[j-2] if 2<=j<len(c)+2 else 0) for j in range(m+1))
out={'scope':'odd m=1,3,...,39; 0<=n<=400 ONLY','sweep':rows,'recurrence_checked_m':[2,41],'obstructions':{'c2_m': '(m)/(4*(2*m-1))','c2_mplus2_minus_m':'-1/(2*(2*m-1)*(2*m+3))','log_coefficient_z4':'-1/(64*(2*m-1)**2*(2*m-3)), m>=3','renewal_z2':'-(m-1)/(4*(2*m-1)), m>=3'},'seconds':time.monotonic()-start}
for m in range(3,40,2):
 c=inverse(q(m),4);d=inverse(q(m+2),2)
 assert c[2]==F(m,4*(2*m-1));assert d[2]-c[2]==-F(1,2*(2*m-1)*(2*m+3))
 log4=c[4]-c[1]*c[3]-c[2]**2/2+c[1]**2*c[2]-c[1]**4/4
 assert log4==-F(1,64*(2*m-1)**2*(2*m-3))
(L/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps({'rows':len(rows),'nonpositive':sum(len(r['nonpositive']) for r in rows),'seconds':out['seconds']}))
