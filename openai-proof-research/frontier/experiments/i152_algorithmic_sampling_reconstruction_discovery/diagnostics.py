"""New I152 finite rational diagnostics; no universal or contribution certification."""
from fractions import Fraction as F
from itertools import product,combinations

def trace_law(x,ps):
 out={}
 for mask in product([0,1],repeat=len(x)):
  w=F(1);y=[]
  for bit,p,keep in zip(x,ps,mask):
   w*=p if keep else 1-p
   if keep:y.append(bit)
  y=tuple(y);out[y]=out.get(y,F(0))+w
 return out

def run():
 checked=0
 for n in range(1,5):
  for x in product([0,1],repeat=n):
   p=F(2,3);law=trace_law(x,[p]*n)
   stats={I:F(0) for k in range(1,n+1) for I in combinations(range(n),k)}
   for y,py in law.items():
    rates=[F(1,j+4) for j in range(len(y))]
    for flip in product([0,1],repeat=len(y)):
     pf=py;u=[]
     for bit,e,f in zip(y,rates,flip):
      pf*=e if f else 1-e;u.append((F(bit^f)-e)/(1-2*e))
     for I in stats:
      if max(I)>=len(y):continue
      v=pf
      for j in I:v*=u[j]
      stats[I]+=v
   for I,val in stats.items():
    expected=sum((py for y,py in law.items() if max(I)<len(y) and all(y[j] for j in I)),F(0))
    assert val==expected;checked+=1
   ps=[F(j+2,j+4) for j in range(n)];law2=trace_law(x,ps);z=F(2,3)
   lhs=sum((py*sum((F(bit)*z**j for j,bit in enumerate(y)),F(0)) for y,py in law2.items()),F(0))
   rhs=F(0);factor=F(1)
   for bit,p in zip(x,ps):rhs+=bit*p*factor;factor*=1-p+p*z
   assert lhs==rhs
 P=trace_law((0,1),[F(1,2)]*2);Q=trace_law((1,0),[F(1,2)]*2);omega=set(P)|set(Q);alpha=F(1,5)
 v=sum((abs(P.get(y,0)-Q.get(y,0)) for y in omega),F(0))/2
 assert v==F(1,4)==alpha/(1-alpha)
 R={y:(1-alpha)*max(P.get(y,0),Q.get(y,0)) for y in omega};assert sum(R.values())==1
 for law in [P,Q]:
  H={y:(R[y]-(1-alpha)*law.get(y,0))/alpha for y in omega}
  assert all(h>=0 for h in H.values()) and sum(H.values())==1
 weighted=[]
 for N in [1,2,4,8,16,64]:
  Z=sum(4**t for t in range(N+1));assert Z==(4**(N+1)-1)//3
  assert Z>=4**N
  weighted.append(dict(N=N,binary_input_bits=N.bit_length(),normalizer_bits=Z.bit_length()))
 # Conservative normalized compiler recurrence: lambda*A=1/4, any r<=1.
 rec=[]
 for r in [F(1),F(1,2),F(1,16)]:
  lam=F(1,1024);A=F(256);u=F(1,10**6);center=F(0)
  for _ in range(17):center=A*u+lam*A*center
  assert center<=A*u/(1-lam*A)
  mean=u+lam*center;sample=r*mean
  assert mean<=F(4,3)*u and sample<=F(4,3)*r*u
  h=F(1,64);a=F(0)
  for _ in range(1000):a=(1-h/2)*a+h*u
  assert a<=2*u
  rec.append(dict(r=str(r),mean_error=str(mean),sample_error=str(sample),outer_error_bound=str(2*u)))
 # The perturbing Jacobian is genuinely nonconservative at the supplied mode.
 eta=F(1,100);J=((F(0),-eta),(eta,F(0)));assert J[1][0]-J[0][1]==2*eta
 return dict(status='PASS',exact_rank_flip_statistics=checked,heterogeneous_first_moment_identities='all binary words of lengths 1..4',actual_trace_huber_example=dict(words=['01','10'],retention='1/2',TV=str(v),alpha=str(alpha)),weighted_binary_examples=weighted,compiler_recurrence_instances=rec,curl_at_zero=str(2*eta),scope='Finite rational checks only. Not a proof of uniform decoding, robust oracle sampling, mixing, substantial contribution, priority or acceptance.')
if __name__=='__main__':
 import json
 print(json.dumps(run(),indent=2))
