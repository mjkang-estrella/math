"""Independent closed-word/matching bijection and weight check over exact integers."""
from itertools import product
cases=0
for n in range(3,11):
 for z in (-2,0,1,3):
  g=[2*k-3 for k in range(n)]
  total=0; matched=0; seen=set()
  for q in product((0,1),repeat=n):
   w=1
   for k in range(n):w*=((1+z,-z*g[k]),(g[k],0))[q[k]][q[(k+1)%n]]
   good=all(not(q[k] and q[(k+1)%n]) for k in range(n))
   if not good:assert w==0
   else:
    s=frozenset(k for k in range(n) if q[(k+1)%n])
    assert s not in seen;seen.add(s)
    assert all((k+1)%n not in s for k in s)
    ends=s|frozenset((k+1)%n for k in s)
    expected=(-z)**len(s)*(1+z)**(n-2*len(s))
    for k in ends:expected*=g[k]
    assert expected==w
    assert tuple(int((k-1)%n in s) for k in range(n))==q
    matched+=expected
   total+=w;cases+=1
  assert total==matched
  assert len(seen)==sum(all(not((m>>k&1) and (m>>((k+1)%n)&1)) for k in range(n)) for m in range(1<<n))
print('PASS',cases,'integer weighted words, n=3..10, including wrap and perfect matchings')
