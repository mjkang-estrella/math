import pathlib,json,math
D=pathlib.Path(__file__).resolve().parents[1]
N=300000;s=bytearray(b'\1')*N;s[0:2]=b'\0\0'
for p in range(2,math.isqrt(N)+1):
 if s[p]:s[p*p:N:p]=b'\0'*len(range(p*p,N,p))
ps=[i for i,v in enumerate(s) if v];pre=[0]
for p in ps:pre.append(pre[-1]+p)
def prime(n):
 if n<N:return bool(s[n])
 for p in ps:
  if p*p>n:return True
  if n%p==0:return False
 raise ValueError(n)
r=[]
for i in range(1,101):
 hits=[k for k in range(3,1000,2) if prime(pre[i+k]-pre[i])]
 r.append(dict(initial_prime=ps[i],odd_lengths_through=999,prime_sum_lengths=hits))
(D/'outputs/prime-sums.json').write_text(json.dumps(r,indent=2)+'\n');print('prime sums: 100 odd initial primes, all odd lengths 3..999; all have hits',all(r0['prime_sum_lengths'] for r0 in r))
from sympy.combinatorics.named_groups import SymmetricGroup, AlternatingGroup, DihedralGroup, CyclicGroup
r=[]
for n in range(3,10):
 for name,G in [('Sym',SymmetricGroup(n)),('Alt',AlternatingGroup(n))]:
  H=G.stabilizer(0).stabilizer(1);orders=[int(H.order())]
  while True:
   K=H.derived_subgroup();orders.append(int(K.order()))
   if K.order()==H.order():break
   H=K
  r.append(dict(group=name,n=n,two_distinct_point_stabilizer_derived_orders=orders,first_perfect_step=len(orders)-2));print(r[-1],flush=True)
(D/'outputs/primitive-groups.json').write_text(json.dumps(r,indent=2)+'\n')
