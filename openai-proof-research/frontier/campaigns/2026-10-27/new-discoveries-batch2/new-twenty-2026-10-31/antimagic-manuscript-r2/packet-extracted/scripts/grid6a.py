import runpy
v=runpy.run_path('scripts/review-verify.py')
for t in (2,4,6):
 for n in (3,4,5):
  a=v['build'](t,n); N=sum(t**h for h in range(1,n)); q=t**(n-1); Z=(N-t)//2+1
  root=sum(a[1]); C=(t//2)*(2*N+t*q+1)+Z
  assert Z<=q and t*Z>=N
  assert 2*root==2*Z+(t-1)*(2*N-t+2)
  assert N<root<=N+t**n and C>N+t**n
  if t>=4:
   assert root>t*Z+N
   for h in range(1,n-1):
    for i in range(t**h):
     w=a[h][i]+sum(a[h+1][t*i:t*(i+1)])
     assert N<w<=N+t**n
  if t==2:
   assert a[2]==[2,2*Z-1,1,2*Z-2]
   assert root==3*Z
   w1=[a[1][i]+sum(a[2][2*i:2*i+2]) for i in range(2)]
   assert w1==[3*Z+1,4*Z-1]
   assert all(w!=root for w in w1)
  assert v['check'](t,n,a)['ok']
  print(t,n,'bounds, root formula, constant and colour tests pass')
