import math,json,pathlib
out=[]
for n in [8,12,16,20,24,32,40,48,64]:
 for pat in ['block','triangle']:
  d=[(1 if i<n//2 else -1) if pat=='block' else (1-4*min(i,n-i)/n) for i in range(n)]
  for eps in [.001,.01,.05]:
   la=[.1+eps*x for x in d];mean=sum(la)/n;rate=1+max(la)
   for frac in [.6,.7,.75,.8,.9]:
    t=n*frac;s=rate*t;v=[1.]*n;w=math.exp(-s);u=[w]*n
    for k in range(1,350):
     v=[v[(i+1)%n]/rate+(1-(1+la[i])/rate)*v[i] for i in range(n)]
     w*=s/k
     for i in range(n):u[i]+=w*v[i]
    gap=sum((1-la[i]/mean)*u[i] for i in range(n))/n
    if gap<0:out.append(dict(n=n,pattern=pat,epsilon=eps,t=t,gap=gap))
print(json.dumps(sorted(out,key=lambda x:x['gap'])[:15],indent=2))
(pathlib.Path(__file__).parent/'cycle-search.json').write_text(json.dumps(out,indent=2))
