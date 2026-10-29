import json
F=[0,1]
for _ in range(26):F.append(sum(F[-2:]))
checks=0;newton_witness=None
for n in range(2,10):
 for m in range(n,19-n):
  A=F[m+1:m+n+1];B=F[1:n+1];D=sum(A)-sum(B)
  h=[0]*(D+1);h[0]=1
  for b in B[1:]:
   for t in range(b,D+1):h[t]+=h[t-b]
  N={0:1}
  for a in A:
   temp=N.copy()
   for k,v in N.items():temp[k+a]=temp.get(k+a,0)-v
   N={k:v for k,v in temp.items() if v}
  delta=[sum(v*h[t-k] for k,v in N.items() if k<=t) for t in range(D+1)]
  p=[0]*(D+1);p[0]=1
  for a in A:
   for t in range(D,a-1,-1):p[t]-=p[t-a]
  for b in B:
   for t in range(b,D+1):p[t]+=p[t-b]
  assert delta==[p[0]]+[p[t]-p[t-1] for t in range(1,D+1)]
  assert all(delta[t]>=0 for t in range(D//2+1))
  for t in range(1,min(80,D)+1):
   L=[0]+[sum(b for b in B[1:] if j%b==0)-sum(a for a in A if j%a==0) for j in range(1,t+1)]
   assert t*delta[t]==sum(L[j]*delta[t-j] for j in range(1,t+1));checks+=1
  if m==5 and n==5:newton_witness={'m':m,'n':n,'j':8,'L_j':sum(b for b in B[1:] if 8%b==0)-sum(a for a in A if 8%a==0),'delta_8':delta[8]}
print(json.dumps({'exact_newton_identities':checks,'genuine_source_log_coefficient_obstruction':newton_witness},indent=2))
