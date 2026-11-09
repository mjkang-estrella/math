from pathlib import Path
import random,json,time,sys,itertools
L=Path(__file__).resolve().parents[1];random.seed(207)
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def add(a,b,s=1):
 c=a[:]+[0]*max(0,len(b)-len(a))
 for i,v in enumerate(b):c[i]=(c[i]+s*v)%3
 return trim(c)
def rem(a,b):
 a=a[:];z=pow(b[-1],-1,3)
 for i in range(len(a)-len(b),-1,-1):
  x=a[i+len(b)-1]*z%3
  if x:
   for j,v in enumerate(b):a[i+j]=(a[i+j]-x*v)%3
 return trim(a)
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%3
 return trim(c)
def power(a,n,m):
 c=[1]
 while n:
  if n&1:c=rem(mul(c,a),m)
  a=rem(mul(a,a),m);n//=2
 return c
def gcd(a,b):
 while b!=[0]:a,b=b,rem(a,b)
 return [(x*pow(a[-1],-1,3))%3 for x in a]
def div(a,b):
 a=a[:];c=[0]*(len(a)-len(b)+1)
 for i in range(len(c)-1,-1,-1):
  x=a[i+len(b)-1]*pow(b[-1],-1,3)%3;c[i]=x
  for j,v in enumerate(b):a[i+j]=(a[i+j]-x*v)%3
 assert trim(a)==[0]
 return trim(c)
def factor(a,f):
 if len(a)-1==f:return [a]
 for attempt in range(100):
  b=[random.randrange(3) for _ in range(len(a)-1)];g=gcd(a,add(power(b,(3**f-1)//2,a),[1],-1))
  if 1<len(g)<len(a):return factor(g,f)+factor(div(a,g),f)
 raise RuntimeError('factor failed')
n=int(sys.argv[1]);f=1
while pow(3,f,n)!=1:f+=1
fs=factor([1]*n,f);fs.sort();out={'n':n,'ord':f,'nontrivial_irreducible_factors_ascending_coefficients':fs};(L/f'outputs/codes-factors-{n}.json').write_text(json.dumps(out,indent=2));print(json.dumps(out),flush=True)
# Generate all full-weight binary-sign vectors for small n and locate minimal cyclic ideals via polynomial gcd.
if n<22:
 hits={}
 xn=[2]+[0]*(n-1)+[1]
 for bits in range(1<<(n-1)):
  v=[1]+[1+((bits>>(j-1))&1) for j in range(1,n)];g=gcd(xn,v);key=tuple(g);hits[key]=v
 nofull=[]
 factors=[[2,1]]+fs
 for mask in range(1<<len(factors)):
  g=[1]
  for j,a in enumerate(factors):
   if mask>>j&1:g=mul(g,a)
  if not any(rem(list(h),g)==[0] for h in hits):nofull.append(mask)
 out['full_weight_vectors_up_to_negation']=1<<(n-1);out['cyclic_code_count']=1<<len(factors);out['no_full_weight_masks']=nofull;out['no_full_weight_count']=len(nofull)
 (L/f'outputs/codes-{n}.json').write_text(json.dumps(out,indent=2));print('COUNT',len(nofull),flush=True)
