from fetch import D
import math,json
N=2000;R=40
pr=bytearray(b'\1')*(N+1);pr[:2]=b'\0\0'
for p in range(2,math.isqrt(N)+1):
 if pr[p]:pr[p*p:N+1:p]=b'\0'*len(range(p*p,N+1,p))
# Encode cyclic polynomials by Kronecker substitution; base is large enough that
# each convolution coefficient (<r*n^2) occupies its own digit without carries.
def mul(a,b,n,r):
 bits=(r*n*n).bit_length();mask=(1<<bits)-1
 x=sum(v<<(bits*i) for i,v in enumerate(a));y=sum(v<<(bits*i) for i,v in enumerate(b));z=x*y
 out=[0]*r
 for i in range(2*r-1):out[i%r]=(out[i%r]+(z&mask))%n;z>>=bits
 return out
pairs=eligible=0;fails=[]
for n in range(2,N+1):
 for r in range(2,R+1):
  if math.gcd(n,r)!=1:continue
  pairs+=1
  if pr[n] or n*n%r==1:continue
  eligible+=1;a=[0]*r;a[0]=n-1;a[1]=1;b=[0]*r;b[0]=1;want=[0]*r;want[n%r]=1;want[0]=(want[0]-1)%n;e=n
  while e:
   if e&1:b=mul(a,b,n,r)
   a=mul(a,a,n,r);e>>=1
  if b==want:fails.append([n,r])
o={'space':f'all 2<=n<={N}, 2<=r<={R}; gcd=1 pairs; skip prime n and n^2=1 mod r since conclusion already true','coprime_pairs':pairs,'eligible':eligible,'violations':fails,'arithmetic':'exact cyclic convolution via carry-free Kronecker substitution; diagnostic, not a Lean certificate'}
(D/'outputs/agrawal.json').write_text(json.dumps(o,indent=2));print(o)
