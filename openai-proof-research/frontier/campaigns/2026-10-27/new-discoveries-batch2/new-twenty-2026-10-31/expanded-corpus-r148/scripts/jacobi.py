import math,json,pathlib,itertools,time,sys
L=pathlib.Path(__file__).resolve().parents[1]
N=int(sys.argv[1]); C=lambda n,k:math.comb(n,k) if 0<=k<=n else 0
E=[[0]*(N+2) for _ in range(N+1)]; E[1][1]=1
for n in range(2,N+1):
 for k in range(n,0,-1):E[n][k]=E[n-1][n-k]+E[n][k+1]
euler=[1]+[sum(E[n]) for n in range(1,N+1)]
D=[None,None]; out=[]
for n in range(2,N+1):
 d={}
 for a in range(2,n+1):
  d[a,1]=E[n-1][a-1]
  for b in range(2,a):
   total=0
   for r in range(2,n,2):
    for x in range(2,r+1):
     for y in range(1,x):
      total+=D[r][x,y]*C(b-2,y-1)*C(a-b-1,x-y-1)*C(n-a,r-x)*euler[n-1-r]
   d[a,b]=total
 D.append(d)
 bad=[(a,b,t,E[n-1][a-b]) for (a,b),t in d.items() if t!=E[n-1][a-b]]
 out.append({'n':n,'total':sum(d.values()),'expected_total':euler[n],'mismatches':bad,'distinct_endpoint_pairs':len(d)})
 print(out[-1],flush=True)
(L/f'outputs/jacobi-{N}.json').write_text(json.dumps(out,indent=2))
