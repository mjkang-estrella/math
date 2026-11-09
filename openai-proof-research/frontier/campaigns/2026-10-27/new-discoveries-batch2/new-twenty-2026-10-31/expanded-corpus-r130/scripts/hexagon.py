import sys,json
N=int(sys.argv[1]);K=int(sys.argv[2])
for s in [1,2,3,4]:
 a=[0]*(N+1);a[0]=1
 for p in range(1,N+1):
  allowed=(p%2==1 or p%10 in [s,10-s]) if s%2==0 else (p%10 not in [0,s,10-s] and p%20 not in [10-2*s,10+2*s])
  if allowed:
   for n in range(p,N+1):a[n]+=a[n-p]
 mono=[n for n in range(2,N+1) if a[n]<a[n-2]]
 sparse=[0]*(N+1)
 for j in range(-N,N+1):
  if s%2==0:
   es=[j*(15*j+3*s-5)//2,(3*j-s//2)*(5*j-3+s//2)//2];sg=(-1)**(j*((s-1)*j-1)//2)
  else:es=[j*(5*j-s)//2];sg=(-1)**(j*(j+s)//2)
  for e in es:
   if 0<=e<=N:sparse[e]+=sg
 full=a[:]
 for j in range(1,int((N/2)**.5)+1):
  e=2*j*j
  for n in range(e,N+1):full[n]+=2*(-1)**j*a[n-e]
 print(json.dumps(dict(s=s,N=N,identity_bad=[n for n in range(N+1) if full[n]!=sparse[n]][:10],two_step_monotonicity_bad=mono[:10])),flush=True)
 for k in range(1,K+1):
  b=a[:]
  for j in range(1,k+1):
   e=2*j*j
   for n in range(e,N+1):b[n]+=2*(-1)**j*a[n-e]
  bad=[n for n in range(N+1) if (-1)**k*(b[n]-sparse[n])<0]
  print(json.dumps(dict(s=s,k=k,bad_count=len(bad),bad_first=bad[:10])),flush=True)
