import json,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1];N=int(sys.argv[1]);maxd=int(sys.argv[2])
# q: sum_m q^(a*m+d*m*(m-1)/2)/(q;q)_m
p=[[1]+[0]*N]
for m in range(1,int((2*N)**.5)+2):
 row=p[-1].copy()
 for n in range(m,N+1):row[n]+=row[n-m]
 p.append(row)
count=0;bad=[]
for d in range(1,maxd+1):
 for a in range(1,d+3):
  q=[0]*(N+1)
  for m in range(len(p)):
   shift=a*m+d*m*(m-1)//2
   if shift>N:break
   for n in range(shift,N+1):q[n]+=p[m][n-shift]
  Q=[1]+[0]*N
  for t in range(1,N+1):
   if t in (a,d+3-a) or t%(d+3) not in {a%(d+3),(-a)%(d+3)}:continue
   for n in range(t,N+1):Q[n]+=Q[n-t]
  neg=[(n,q[n],Q[n]) for n in range(1,N+1) if q[n]<Q[n]]
  if neg:bad.append(dict(d=d,a=a,first=neg[0],last=neg[-1],count=len(neg)))
  count+=1
print(json.dumps(dict(N=N,maxd=maxd,parameter_pairs=count,bad=bad),indent=2))
