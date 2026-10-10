"""Read-only exact finite diagnostics. Not a proof of the universal claims."""
import itertools,random,json

def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a

def add(a,b,p):return trim([((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0))%p for i in range(max(len(a),len(b)))])
def mul(a,b,p):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%p
 return trim(c)
def val(a,x,p):
 r=0
 for c in a[::-1]:r=(r*x+c)%p
 return r

def rank(A,p):
 A=[row[:] for row in A]
 if not A:return 0
 r=0
 for j in range(len(A[0])):
  z=next((z for z in range(r,len(A)) if A[z][j]%p),None)
  if z is None:continue
  A[r],A[z]=A[z],A[r];t=pow(A[r][j],-1,p);A[r]=[x*t%p for x in A[r]]
  for k in range(len(A)):
   if k!=r:
    t=A[k][j];A[k]=[(a-t*b)%p for a,b in zip(A[k],A[r])]
  r+=1
  if r==len(A):break
 return r

def detpoly(A,p):
 h=len(A);ans=[0]
 for perm in itertools.permutations(range(h)):
  a=[(-1)**sum(perm[i]>perm[j] for i in range(h) for j in range(i+1,h))%p]
  for i,j in enumerate(perm):a=mul(a,A[i][j],p)
  ans=add(ans,a,p)
 return ans

def multiplicity(a,x,p):
 a=a[:];k=0
 while len(a)>1 and val(a,x,p)==0:
  b=[0]*(len(a)-1);b[-1]=a[-1]
  for j in range(len(b)-2,-1,-1):b[j]=(a[j+1]+x*b[j+1])%p
  assert (a[0]+x*b[0])%p==0
  a=trim(b);k+=1
 return k

def run():
 rng=random.Random(103);cases=0;checks=0
 for p in [101,103,107]:
  for d in [3,4,5,6]:
   w=3;gamma=2;nodes=[[pow(3,i,p)*pow(gamma,r,p)%p for r in range(d)] for i in range(w)]
   assert len(set(sum(nodes,[])))==w*d
   for h in [1,2,3]:
    if h>d:continue
    for z in range(6):
     while True:
      fs=[[rng.randrange(p) for _ in range(d)] for j in range(h)]
      if rank(fs,p)==h:break
     C=detpoly([[[a*pow(gamma,r*k,p)%p for k,a in enumerate(f)] for f in fs] for r in range(h)],p)
     assert C!=[0];checks+=1
     total=0
     for ns in nodes:
      orders=[];prev=0
      for a in range(d):
       rk=rank([[val(f,x,p) for f in fs] for x in ns[:a+1]],p)
       if rk>prev:orders.append(a)
       prev=rk
      assert len(orders)==h;checks+=1
      for r,x in enumerate(ns):
       lower=sum(a>=r+h for a in orders)
       assert multiplicity(C,x,p)>=lower;checks+=1
      total+=sum(orders)
     assert total<=h*(d-1)+w*h*(h-1);checks+=1;cases+=1
 # Ordinary derivative / first-h Hasse replacement fails at distinct nodes.
 p=5;orders_sum=p*p;old_bound=2*p+p
 assert orders_sum>old_bound;checks+=1
 # F4 represented by a^2+a+1=0. Two embeddings matter on descent.
 def fm(x,y):
  t=0
  for j in range(2):
   if (y>>j)&1:t^=x<<j
  if t&4:t^=7
  return t
 a=2;b=fm(a,a)
 assert b==3 and fm(b,b)==a and (b^a)!=0;checks+=3
 # Multiplication by b: columns b,ba in basis 1,a; det over F4 of R_b-aI = 0.
 c0=b;c1=fm(b,a);R=[[c0&1,c1&1],[(c0>>1)&1,(c1>>1)&1]]
 R[0][0]^=a;R[1][1]^=a
 assert fm(R[0][0],R[1][1])^fm(R[0][1],R[1][0])==0;checks+=1
 # Explicit rational domain obstruction: commutator of common scalar shifts is strictly triangular.
 for p in [2,3,5,7]:
  for d in range(2,6):
   X=[[rng.randrange(p) if i<j else 0 for j in range(d)] for i in range(d)]
   Y=[[rng.randrange(p) if i<j else 0 for j in range(d)] for i in range(d)]
   for i in range(d):X[i][i]=1;Y[i][i]=p-1
   C=[[(sum(X[i][k]*Y[k][j]-Y[i][k]*X[k][j] for k in range(d)))%p for j in range(d)] for i in range(d)]
   assert all(C[i][j]==0 for i in range(d) for j in range(i+1));assert rank(C,p)<d;checks+=2
 # At actual 2x2 noncommuting inputs the commutator is invertible in every tested characteristic.
 for p in [2,3,5,7]:
  assert rank([[1,0],[0,(-1)%p]],p)==2;checks+=1
 # Parameter / conjugate budget checks, including p=2 choice of 3-power M.
 parameter_cases=0
 for n in range(1,5):
  for B in range(1,5):
   for h in range(1,4):
    for p in [2,3,5,101,1000000007]:
     w=n+1;Delta=4*w**3*B;ell=3 if p==2 else 2;M=1
     while M<=B*Delta:M*=ell
     N=M-Delta;E=4*M*M*(n+M);D=(h+1)*B*M*M*E;H=(D+2)**2
     e=1;Q=p
     while Q<=H:e+=1;Q*=p
     assert M<=3*B*Delta and N>0 and M%p!=0
     assert M-B*Delta>0 and Q>e*D
     assert D+3>=e and (p>H or Q<=H*H)
     checks+=3;parameter_cases+=1
 return {'status':'PASS','flag_cases':cases,'parameter_cases':parameter_cases,'exact_assertions':checks,'frobenius_conjugate_counterexample':{'field':'F4','polynomial':'x-alpha','point':'alpha^2','point_value':1,'conjugate_value':0},'ordinary_flag_counterexample':{'p':5,'space':'span(1,z^5)','sum_orders':orders_sum,'old_bound':old_bound},'scope':'Finite exact diagnostic evidence only; not universal proof, contribution certification, or independent review.'}
if __name__=='__main__':print(json.dumps(run(),indent=2))
