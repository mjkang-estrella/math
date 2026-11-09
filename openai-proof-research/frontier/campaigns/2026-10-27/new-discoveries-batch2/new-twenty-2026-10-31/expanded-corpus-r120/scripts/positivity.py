import json
from pathlib import Path
D=Path(__file__).resolve().parents[1];L=2500;count=0;worst=0
for a in range(1,25):
 m=a+1
 for N in range(1,13):
  for M in range(N,13):
   f=[1]+[0]*L
   for j in range(N):
    d=a+m*j
    for k in range(d,L+1):f[k]-=f[k-d]
   for j in range(M):
    d=1+m*j
    for k in range(d,L+1):f[k]+=f[k-d]
   for j in range(N+M-1):
    d=m*(j+1)
    for k in range(L,d-1,-1):f[k]+=f[k-d]
   count+=1
   if min(f)<0:
    print('NEGATIVE',a,N,M,next((k,v) for k,v in enumerate(f) if v<0),flush=True);raise SystemExit
 print('completed a',a,'all 1<=N<=M<=12 degrees0..2500',flush=True)
print(json.dumps(dict(parameter_triples=count,degree_max=L,b=1,scaling='b divides a permits q -> q^b; tested a/b=1..24',finding='no negative coefficient')))
