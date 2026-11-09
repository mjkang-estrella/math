import pathlib,json,math
D=pathlib.Path(__file__).resolve().parents[1];N=3000;p=[1]
for n in range(1,N+1):
 v=0
 for j in range(1,n+1):
  g=j*(3*j-1)//2
  if g>n:break
  sign=1 if j%2 else -1;v+=sign*p[n-g];g=j*(3*j+1)//2
  if g<=n:v+=sign*p[n-g]
 p.append(v)
primes=[k for k in range(2,p[-1].bit_length()+1) if all(k%d for d in range(2,math.isqrt(k)+1))]
def root(v,k):
 if k==2:return math.isqrt(v)
 lo=1;hi=1<<((v.bit_length()+k-1)//k)
 while lo+1<hi:
  m=(lo+hi)//2
  if m**k<=v:lo=m
  else:hi=m
 return hi if hi**k==v else lo
hits=[];checks=0
for n in range(2,N+1):
 for k in primes:
  if k>=p[n].bit_length():break
  m=root(p[n],k);checks+=1
  if m>=2 and m**k==p[n]:hits.append([n,m,k])
out={'range':[2,N],'exponents':'all prime exponents up to bit length, hence all perfect powers','checks':checks,'hits':hits,'p_end':str(p[-1]),'limitation':'No conclusion for finiteness of near powers'};print(out);(D/'outputs/partition.json').write_text(json.dumps(out,indent=2))
